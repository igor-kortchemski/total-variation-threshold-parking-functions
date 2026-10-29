#!/usr/bin/env bash
# Local/private standalone verification. This is not Palomar's full preflight.
# The outcome policy is pinned to PalomarSubmission 14aa8d6b3c2f14a8540605e37144560b9a00e7e7.
set -euo pipefail
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"
for command_name in bwrap lake lean python3; do
  command -v "$command_name" >/dev/null || { echo "Missing $command_name" >&2; exit 1; }
done
[ "$(uname -s)" = Linux ] || { echo 'Supported Linux with Bubblewrap is required.' >&2; exit 1; }
: "${PALOMAR_CON_RON:?Set this to the authenticated official Lean 4.36.0-rc1 con-ron executable}"
: "${PALOMAR_OUTCOME_POLICY:?Set this to the pinned official kernel_outcomes.py}"
: "${PALOMAR_STANDALONE_OUTPUT:?Set this to a fresh evidence directory outside the source checkout}"
export PALOMAR_LEAN_PREFIX
PALOMAR_LEAN_PREFIX=$(lean --print-prefix)
python3 -I - <<'PY'
import hashlib, importlib.util, json, os, pathlib, re, shutil, signal, subprocess, sys, time

POLICY = '14aa8d6b3c2f14a8540605e37144560b9a00e7e7'
CON_RON_SHA = '4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef'
OUTCOME_SHA = '63329382f969ca8280661076ab4ce7dc1d9a1b54083d2c8a9d57a25a16486e79'
repo = pathlib.Path.cwd().resolve()
prefix = pathlib.Path(os.environ['PALOMAR_LEAN_PREFIX']).resolve()
out = pathlib.Path(os.environ['PALOMAR_STANDALONE_OUTPUT']).resolve()
con_ron = pathlib.Path(os.environ['PALOMAR_CON_RON']).resolve()
policy_file = pathlib.Path(os.environ['PALOMAR_OUTCOME_POLICY']).resolve()
bwrap = pathlib.Path(os.environ.get('COMPARATOR_BWRAP') or shutil.which('bwrap')).resolve()
assert not out.is_relative_to(repo), 'Evidence must be outside the candidate checkout.'
out.mkdir(parents=True, exist_ok=True)
assert not (out / 'standalone-report.json').exists(), 'Choose a fresh evidence directory.'
started = time.monotonic()
deadline = started + 19800
report = {'kind': 'private-standalone-comparator', 'official_palomar_full_preflight': False,
          'status': 'not_verified', 'mandatory_status': 'not_verified', 'kernels': [],
          'kernel_attempts': [], 'controls': {}, 'pipeline_policy_commit': POLICY,
          'source_commit': os.environ.get('GITHUB_SHA'), 'repository': os.environ.get('GITHUB_REPOSITORY'),
          'run_id': os.environ.get('GITHUB_RUN_ID'), 'run_attempt': os.environ.get('GITHUB_RUN_ATTEMPT'),
          'scope': 'Exact local source snapshot; supported Comparator with Lean and NanoDa; separate pinned con-ron replay. No registry submission or registration.'}

def sha(path):
    with pathlib.Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def save():
    (out / 'standalone-report.json').write_text(json.dumps(report, indent=2) + '\n')

def snapshot():
    result = {}
    for directory, dirs, files in os.walk(repo):
        dirs[:] = sorted(d for d in dirs if d not in {'.git', '.lake', '.scratch'})
        for filename in sorted(files):
            if filename == '.DS_Store':
                continue
            path = pathlib.Path(directory) / filename
            assert not path.is_symlink(), f'Source symlink is not supported: {path}'
            result[str(path.relative_to(repo))] = sha(path)
    return result

def run(argv, label, *, cwd=repo, stdout_path=None, timeout=None):
    seconds = min(timeout or 19800, max(0, deadline - time.monotonic() - 60))
    if seconds < 1:
        raise TimeoutError('Shared standalone verification budget exhausted.')
    print(f'[{label}]', flush=True)
    with (out / 'commands.jsonl').open('a') as f:
        f.write(json.dumps({'stage': label, 'argv': list(map(str, argv)), 'cwd': str(cwd), 'timeout': seconds}) + '\n')
    stdout = pathlib.Path(stdout_path) if stdout_path else out / (label + '.stdout.log')
    stderr = out / (label + '.stderr.log')
    with stdout.open('wb') as fo, stderr.open('wb') as fe:
        proc = subprocess.Popen(list(map(str, argv)), cwd=cwd, stdout=fo, stderr=fe, start_new_session=True)
        try:
            code = proc.wait(timeout=seconds)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
            raise TimeoutError(f'{label} exceeded its bounded budget.')
    return code, stdout, stderr

def must(argv, label, **kw):
    code, stdout, stderr = run(argv, label, **kw)
    if code:
        raise RuntimeError(f'{label} failed with exit {code}; inspect {stderr.name}.')
    return stdout

# Separate filesystem namespaces expose only system runtimes, the fixed toolchain,
# and explicitly selected inputs. Candidate compilation can write only its .lake.
# This standalone policy is narrower than mounting the host root, but is not a
# claim to implement Palomar's separate seccomp/cgroup/allowlist preflight.
def sandbox(argv, *, cwd, readable=(), writable=(), env=None):
    args = [str(bwrap), '--unshare-all', '--new-session', '--die-with-parent', '--clearenv']
    for name in ('/usr', '/bin', '/lib', '/lib64'):
        path = pathlib.Path(name)
        if path.is_symlink():
            args += ['--symlink', os.readlink(path), name]
        elif path.exists():
            args += ['--ro-bind', name, name]
    args += ['--dir', '/home', '--dir', '/root', '--dir', '/run/user', '--dir', '/var',
             '--proc', '/proc', '--dev', '/dev', '--tmpfs', '/tmp', '--dir', '/tmp/home']
    for name in ('/etc/ld.so.cache', '/etc/localtime', '/etc/passwd', '/etc/group', '/etc/nsswitch.conf'):
        if pathlib.Path(name).exists():
            args += ['--ro-bind', name, name]
    for path in dict.fromkeys([prefix, bwrap, *map(pathlib.Path, readable)]):
        args += ['--ro-bind', str(path), str(path)]
    for path in dict.fromkeys(map(pathlib.Path, writable)):
        args += ['--bind', str(path), str(path)]
    values = {'PATH': f'{prefix}/bin:/usr/bin:/bin', 'HOME': '/tmp/home', 'TMPDIR': '/tmp',
              'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8', 'LEAN_ABORT_ON_PANIC': '1',
              'LEAN_NUM_THREADS': '2', 'COMPARATOR_BWRAP': str(bwrap)}
    values.update(env or {})
    for key, value in values.items():
        args += ['--setenv', key, str(value)]
    return args + ['--chdir', str(cwd), '--', *map(str, argv)]

def exports_for(config, primitives):
    axioms = config['permitted_axioms']
    quot = ['Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind'] if 'Quot.sound' in axioms else []
    return quot + config['theorem_names'] + axioms + primitives + config.get('definition_names', [])

def export(module, targets, output, *, cwd, readable, lean_path, label):
    must(sandbox([prefix / 'bin/leanexport', module, '--', *targets], cwd=cwd,
                 readable=readable, env={'LEAN_PATH': lean_path}), label, cwd=cwd, stdout_path=output)
    with output.open('rb') as f:
        assert f.readline(4096).startswith(b'{"meta":'), 'Exporter produced no NDJSON header.'
    output.chmod(0o444)

def judge(config, challenge, solution, label):
    work = out / (label + '-work'); work.mkdir()
    return run(sandbox([prefix / 'bin/lake', 'comparator', '--config', config,
                        '--challenge-from-export', challenge, '--solution-from-export', solution],
                       cwd=work, readable=[config, challenge, solution], writable=[work]), label, cwd=work)

def accepted(result):
    code, stdout, stderr = result
    log = stdout.read_text() + '\n' + stderr.read_text()
    return code == 0 and all(s in log for s in ['Your solution is okay!',
        'nanoda kernel accepts the solution', 'Lean default kernel accepts the solution'])

def advisory(exported, label, *, control=False):
    work = out / (label + '-work'); work.mkdir()
    try:
        code, stdout, stderr = run(sandbox([con_ron, '--jobs=2', '--verified', exported], cwd=work,
            readable=[con_ron, exported, work]), label, cwd=work, timeout=1800)
        outcome = outcome_policy.con_ron_outcome(code, stdout.read_text(), stderr.read_text())
    except TimeoutError as error:
        if control:
            raise
        outcome = {'name': 'con-ron', 'status': 'declined', 'reason': 'capacity',
                   'exit_code': None, 'detail': str(error)}
    outcome['binary_sha256'] = sha(con_ron)
    outcome['release'] = 'v4.36.0-rc1'
    outcome['solution_export_sha256'] = sha(exported)
    outcome['budget_seconds'] = 1800
    return outcome

try:
    assert (repo / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0', 'This pinned standalone wrapper supports Lean 4.35.0.'
    assert sha(con_ron) == CON_RON_SHA, 'con-ron does not match the official checker revision.'
    assert sha(policy_file) == OUTCOME_SHA, 'Outcome parser does not match the pinned official source.'
    spec = importlib.util.spec_from_file_location('pinned_kernel_outcomes', policy_file)
    outcome_policy = importlib.util.module_from_spec(spec); spec.loader.exec_module(outcome_policy)
    tools = {name: prefix / 'bin' / name for name in ('lean', 'lake', 'leanexport', 'leanchecker', 'nanoda_bin')}
    assert all(p.is_file() and os.access(p, os.X_OK) for p in tools.values())
    report['tool_digests'] = {name: sha(path) for name, path in {**tools, 'bwrap': bwrap, 'con-ron': con_ron}.items()}
    report['outcome_policy_sha256'] = OUTCOME_SHA
    original = snapshot()
    (out / 'source-files.sha256.json').write_text(json.dumps(original, indent=2) + '\n')
    report['source_snapshot_sha256'] = hashlib.sha256(json.dumps(original, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    config = json.loads((repo / 'comparator.json').read_text())
    assert 'external_kernels' not in config, 'Submitted external_kernels is forbidden.'
    assert set(config['permitted_axioms']) == {'propext', 'Quot.sound', 'Classical.choice'}
    report['comparator_config_sha256'] = sha(repo / 'comparator.json')
    report['library_build'] = 'lake build (all configured default targets)'
    report['theorem_names'] = config['theorem_names']
    report['permitted_axioms'] = config['permitted_axioms']
    config.pop('enable_nanoda', None)
    config['external_kernels'] = {'nanoda': [str(tools['nanoda_bin'])]}
    protected_config = out / 'mandatory-comparator.json'
    protected_config.write_text(json.dumps(config, indent=2) + '\n'); protected_config.chmod(0o444)
    source = (prefix / 'src/lean/lake/Lake/CLI/Check.lean').read_text()
    body = re.search(r'^def primitiveTargets[^\n]*\n(.*?)^def ', source, re.M | re.S).group(1)
    body = re.sub(r'/-.*?-/', '', body, flags=re.S)
    body = '\n'.join(line.split('--', 1)[0] for line in body.splitlines())
    literal = re.fullmatch(r'\s*return\s*#\[([^\[\]]*)\]\s*', body)
    assert literal, 'Unrecognized official primitive target list.'
    primitives = []
    for item in literal.group(1).split(','):
        if item.strip():
            match = re.fullmatch(r'``([A-Za-z_][A-Za-z0-9_\'.]*)', item.strip())
            assert match, 'Unrecognized primitive target.'
            primitives.append(match.group(1))
    assert primitives and len(primitives) == len(set(primitives))

    # Judge controls are isolated from the candidate and run before its build.
    controls = out / 'controls'; controls.mkdir()
    library = controls / 'lib'; library.mkdir()
    control_config = {**config, 'challenge_module': 'ControlGood', 'solution_module': 'ControlGood',
                      'theorem_names': ['palomar_control'], 'definition_names': []}
    cc = controls / 'comparator.json'; cc.write_text(json.dumps(control_config))
    texts = {'ControlGood': 'theorem palomar_control : True := trivial\n',
             'ControlWrong': 'theorem palomar_control : True ∧ True := ⟨trivial, trivial⟩\n',
             'ControlAxiom': 'axiom palomar_forbidden : True\ntheorem palomar_control : True := palomar_forbidden\n'}
    lp = f'{library}:{prefix}/lib/lean'
    for module, text in texts.items():
        src = controls / (module + '.lean'); src.write_text(text)
        must(sandbox([tools['lean'], '-o', library / (module + '.olean'), src], cwd=controls,
                     readable=[controls], writable=[library], env={'LEAN_PATH': lp}), 'compile-' + module, cwd=controls)
        export(module, exports_for(control_config, primitives), controls / (module + '.export'),
               cwd=controls, readable=[controls], lean_path=lp, label='export-' + module)
    good = controls / 'ControlGood.export'
    records = [json.loads(line) for line in good.read_bytes().splitlines() if line.strip()]
    index = next(r['in'] for r in records if 'in' in r and r.get('str', {}).get('str') == 'palomar_control')
    theorem = next(r['thm'] for r in records if isinstance(r.get('thm'), dict) and r['thm']['name'] == index)
    theorem['value'] = theorem['type']
    bad = controls / 'ControlIllTyped.export'
    bad.write_text(''.join(json.dumps(r, separators=(',', ':')) + '\n' for r in records)); bad.chmod(0o444)
    assert accepted(judge(cc, good, good, 'control-matching')), 'Matching control failed.'
    report['controls']['matching'] = 'passed'
    for name, expected in [('ControlWrong', 'Challenge and solution theorem statement do not match'),
                           ('ControlAxiom', 'Illegal axiom detected'),
                           ('ControlIllTyped', 'Lean default kernel rejected the solution')]:
        code, stdout, stderr = judge(cc, good, controls / (name + '.export'), 'control-' + name)
        log = stdout.read_text() + '\n' + stderr.read_text()
        assert code != 0 and expected in log, f'{name} negative control failed.'
        if name == 'ControlIllTyped':
            assert 'nanoda kernel rejected the solution' in log, 'NanoDa did not reject the ill-typed control.'
        report['controls'][name] = 'passed'
    for path, expected in [(good, 'accepted'), (bad, 'rejected')]:
        outcome = advisory(path, 'control-con-ron-' + expected, control=True)
        assert outcome['status'] == expected, 'Pinned con-ron control failed.'
        report['controls']['con-ron-' + expected] = 'passed'
    save()

    # Cache bootstrap may download authenticated Mathlib artifacts. Subsequent
    # candidate build, exports, comparison and checkers have no network.
    must([tools['lake'], 'exe', 'cache', 'get'], 'mathlib-cache')
    (repo / '.lake').mkdir(exist_ok=True)
    must(sandbox([tools['lake'], 'build'],
                 cwd=repo, readable=[repo], writable=[repo / '.lake']), 'candidate-build')
    lp_file = must(sandbox([tools['lake'], 'env', '/usr/bin/printenv', 'LEAN_PATH'], cwd=repo,
                          readable=[repo], writable=[repo / '.lake']), 'candidate-lean-path')
    lean_path = lp_file.read_text().strip(); assert lean_path
    exports = out / 'exports'; exports.mkdir()
    challenge = exports / 'Challenge.export'; solution = exports / 'Solution.export'
    for module, output in [(config['challenge_module'], challenge), (config['solution_module'], solution)]:
        export(module, exports_for(config, primitives), output, cwd=repo, readable=[repo],
               lean_path=lean_path, label='candidate-export-' + output.stem)
    export_hashes = {'challenge': sha(challenge), 'solution': sha(solution)}
    report['export_sha256'] = export_hashes
    assert accepted(judge(protected_config, challenge, solution, 'mandatory-comparator')), 'Mandatory Comparator/Lean/NanoDa verification failed.'
    report['mandatory_status'] = 'passed'; report['kernels'] = ['Lean', 'NanoDa']
    save()
    outcome = advisory(solution, 'advisory-con-ron')
    report['kernel_attempts'].append(outcome)
    assert outcome['status'] in {'accepted', 'declined'}, 'Advisory checker rejected the proof or failed without a recognized decline.'
    if outcome['status'] == 'accepted':
        report['kernels'].append('con-ron')
    assert {'challenge': sha(challenge), 'solution': sha(solution)} == export_hashes, 'An export changed during judging.'
    assert snapshot() == original, 'Candidate source files changed during verification.'
    report['source_integrity'] = 'passed'
    report['status'] = 'passed'
except BaseException as error:
    report['error'] = f'{type(error).__name__}: {error}'
    print(report['error'], file=sys.stderr, flush=True)
finally:
    report['elapsed_seconds'] = round(time.monotonic() - started, 3)
    if 'original' in globals():
        report['source_integrity'] = 'passed' if snapshot() == original else 'failed'
        if report['source_integrity'] != 'passed':
            report['status'] = 'not_verified'
    save()
    print(json.dumps({k: report[k] for k in ('status', 'mandatory_status', 'kernels', 'kernel_attempts', 'controls')}, indent=2), flush=True)
sys.exit(0 if report['status'] == 'passed' else 1)
PY
