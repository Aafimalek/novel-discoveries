from pathlib import Path
import json
labels='bxXyYZa'
f=Path('mix-prefix').read_text()
rows=json.loads(Path('cert.json').read_text())
for terms,L,ord in rows:
 f+='  ·\n'
 for pair,c in terms:
  if pair=='ba':
   f+='    have hb := base (by decide)\n'
  else:
   f+=f'    have h{pair} := strong ({c},{labels.index(pair[0])},{labels.index(pair[1])}) (by decide)\n'
 f+='    simp [linearForm, cert, coeff, start, finish] at upper\n'
 hs=['hb' if pair=='ba' else 'h'+pair for pair,c in terms]
 f+='    simp only [start, finish] at '+' '.join(h for h in hs if h!='hb')+'\n'
 f+='    omega\n'
Path('TwoByThreeMixtures.lean').write_text(f+Path('mix-suffix').read_text())
