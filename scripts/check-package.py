#!/usr/bin/env python3
"""Fail-closed local checks for the approved export; not Palomar certification."""
from pathlib import Path
import hashlib,json,os,re
root=Path(__file__).resolve().parent.parent

def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def code_only(text):
    out=[];i=0;depth=0;string=False
    while i<len(text):
        if depth:
            if text.startswith('/-',i):depth+=1;i+=2
            elif text.startswith('-/',i):depth-=1;i+=2
            else:i+=1
        elif string:
            c=text[i];out.append(c);i+=1
            if c=='\\' and i<len(text):out.append(text[i]);i+=1
            elif c=='"':string=False
        elif text.startswith('/-',i):depth=1;out.append(' ');i+=2
        elif text.startswith('--',i):
            end=text.find('\n',i);i=len(text) if end<0 else end;out.append(' ')
        else:
            c=text[i];out.append(c);i+=1
            if c=='"':string=True
    assert depth==0 and not string
    return ''.join(out)

production=[root/'Parking.lean',*sorted((root/'Parking').rglob('*.lean'))]
assert len(production)==79
paths=production+[root/'Challenge.lean',root/'Solution.lean']
source_manifest=json.loads((root/'evidence/source-manifest.json').read_text())['files']
assert set(source_manifest)=={p.relative_to(root).as_posix() for p in paths}
imports={}
for p in paths:
    rel=p.relative_to(root).as_posix();text=p.read_text();code=code_only(text)
    assert not p.is_symlink() and digest(p)==source_manifest[rel]['sha256'],rel+' source hash mismatch'
    assert code.lstrip().startswith('module'),rel
    assert len(text.splitlines())<=10000,rel
    assert not re.search(r'\b(admit|axiom|opaque|constant|native_decide|bv_decide|unsafe|partial)\b|Lean\.(ofReduceBool|ofReduceNat|trustCompiler)',code),rel
    holes=re.findall(r'\bsorry\b',code)
    assert len(holes)==(3 if rel=='Challenge.lean' else 0),rel+' unauthorized hole count'
    imports[rel]=re.findall(r'^(?:public\s+)?(?:meta\s+)?import\s+([A-Za-z0-9_.]+)\s*$',code,re.M)
    assert 'Challenge' not in imports[rel],rel+' imports Challenge'
    assert 'SPDX-License-Identifier: Apache-2.0' in text.split('-/',1)[0],rel
assert all(n.startswith('Mathlib.') for n in imports['Challenge.lean'])
expected_modules=['Parking.Frozen.MainBounds','Parking.Frozen.Profile','Parking.Frozen.Decoupling']
assert imports['Solution.lean']==expected_modules
for rel,names in imports.items():
    for module in names:
        if module.startswith('Parking.Frozen.'):
            assert rel=='Solution.lean' and module in expected_modules,(rel,module)
        if module.startswith('Parking.Provider.'):
            assert rel=='Parking/Frozen/'+module.rsplit('.',1)[1]+'.lean',(rel,module)
challenge=(root/'Challenge.lean').read_text();cc=code_only(challenge)
assert len(challenge.splitlines())<=1000 and len(challenge.encode())<=100*1024
reset='run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}'
assert cc.count('run_cmd')==cc.count(reset)==4
blocks=json.loads((root/'evidence/challenge-source-blocks.json').read_text())['blocks']
assert len(blocks)==22 and sum(b['kind']=='frozen_signature' for b in blocks)==3
for item in blocks:
    block=item['verbatim_source_text']
    assert block in challenge and block in (root/item['source']).read_text(),item['source']
    if item['kind']=='frozen_signature':assert block.rstrip('\n')+'\n  by sorry' in challenge
anchors=json.loads((root/'frozen-anchors.json').read_text())['anchors']
assert len(anchors)==3
for a in anchors:
    text=(root/a['path']).read_text();start=text.index('\n',text.index('FROZEN_ANCHOR_PROOF_BEGIN'))+1
    end=text.rfind('\n',0,text.index('FROZEN_ANCHOR_PROOF_END'))+1
    assert hashlib.sha256(text[:start].encode()).hexdigest()==a['prefix_sha256']
    assert hashlib.sha256(text[end:].encode()).hexdigest()==a['suffix_sha256']
    assert text[start:end].strip()=='by exact '+a['implementation']['export']
    assert a['state']=='SEALED'
assert (root/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0'
manifest=json.loads((root/'lake-manifest.json').read_text())
for p in manifest['packages']:
    assert p['type']=='git' and re.fullmatch(r'[0-9a-f]{40}',p['rev'])
    assert p['url'].startswith('https://github.com/') and '@' not in p['url']
assert next(p for p in manifest['packages'] if p['name']=='mathlib')['rev']=='56a005855ea17e0b0958f73ec801ae140b0a1679'
metadata=json.loads('\n'.join(line for line in (root/'formalization.yaml').read_text().splitlines() if not line.lstrip().startswith('#')))
assert metadata['project']['license']=='Apache-2.0'
assert metadata['status']['sorry_count']==metadata['status']['sorry_in_definitions']==0
assert digest(root/'LICENSE')==json.loads((root/'evidence/license-header-update.json').read_text())['license']['sha256']
for base,dirs,names in os.walk(root):
    dirs[:]=[d for d in dirs if d not in {'.git','.lake','.scratch'}]
    for name in names:
        p=Path(base)/name;rel=p.relative_to(root)
        assert not p.is_symlink(),rel
        if p.suffix in {'.md','.json','.in','.lean','.yaml','.yml','.txt','.log'}:
            text=p.read_text()
            assert '/Users/' not in text and '/private/' not in text,rel
            assert not any(ord(c)<32 and c not in '\n\t' for c in text),rel
print('EXPORT CHECK PASS: 79 complete implementation modules, 3 authorized Challenge holes, exact source blocks, sealed successor hashes, licensed/pinned inputs, and import quarantine.')
print('Comparator, NanoDa and the official Palomar full preflight are separate checks.')
