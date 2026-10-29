#!/usr/bin/env python3
"""Prepare deterministic implementation-only audit inputs; Challenge is excluded."""
from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent.parent
paths=[root/'Parking.lean',*sorted((root/'Parking').rglob('*.lean'))]
imports=set();sources={}
for path in paths:
    assert not path.is_symlink(),path
    data=path.read_bytes();text=data.decode();name=path.relative_to(root).as_posix()
    for match in re.finditer(r'^(?:public\s+)?(?:meta\s+)?import\s+([^\n]+)',text,re.M):
        for module in match.group(1).split():
            if module=='--': break
            assert module!='Challenge',name
            if module!='Parking' and not module.startswith('Parking.'): imports.add(module)
    sources[name]={'sha256':hashlib.sha256(data).hexdigest(),'lines':len(text.splitlines())}
report=root/'evidence/audit';report.mkdir(parents=True,exist_ok=True)
(report/'project-modules.txt').write_text(''.join(p.relative_to(root).with_suffix('').as_posix().replace('/','.')+'\n' for p in paths))
(report/'dependency-imports.txt').write_text(''.join(n+'\n' for n in sorted(imports)))
(report/'source-hashes.json').write_text(json.dumps(sources,indent=2)+'\n')
print(f'Audit prepared: {len(paths)} implementation modules; {len(imports)} direct dependency imports; Challenge excluded.')
