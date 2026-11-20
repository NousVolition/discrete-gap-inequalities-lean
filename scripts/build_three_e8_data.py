"""Reconstruct the three-E8 integer witnesses using rational Gaussian elimination.

Run without arguments to regenerate the saved tables, or with --check to compare.
This discovery script is not trusted by Lean: every used identity is kernel-checked.
"""
import sys
from pathlib import Path
from fractions import Fraction as Q
import re, json

root = Path(__file__).resolve().parents[1]
rows = re.findall(r'=> #\[([^\]]+)\]', (root/'GolayMatrixDistance.lean').read_text(encoding='utf-8'))[:12]
gen = [[int(i==j) for j in range(12)] + [int(t=='true') for t in re.findall(r'true|false', row)] for i,row in enumerate(rows)]
words = [[sum(((m>>i)&1)*gen[i][j] for i in range(12))%2 for j in range(24)] for m in range(4096)]
octads = [(m,{j for j,b in enumerate(w) if b}) for m,w in enumerate(words) if sum(w)==8]
ma,A = octads[0]
mb,B = next((m,s) for m,s in octads if not A&s)
C = set(range(24))-A-B
mc = next(m for m,w in enumerate(words) if {j for j,b in enumerate(w) if b}==C)
blocks = [sorted(s) for s in (A,B,C)]
simple = [[2,-2,-2,-2,-2,-2,-2,2],[4,4,0,0,0,0,0,0],[-4,4,0,0,0,0,0,0]]
for i in range(1,6):
    r=[0]*8; r[i]=-4; r[i+1]=4; simple.append(r)
e8 = [simple[i] for i in [7,6,5,4,3,2,0,1]]
base=[]
for block in blocks:
    for r in e8:
        v=[0]*24
        for j,c in zip(block,r): v[j]=c
        base.append(v)
old=[[1]*23+[-3]] + [[2*b for b in gen[i]] for i in range(1,12)]
old += [[4*int(j==i or j==23) for j in range(24)] for i in range(12,23)]
old += [[8*int(j==23) for j in range(24)]]

def inv(a):
    n=len(a); m=[[Q(v) for v in row]+[Q(i==j) for j in range(n)] for i,row in enumerate(a)]
    for j in range(n):
        k=next(k for k in range(j,n) if m[k][j]); m[j],m[k]=m[k],m[j]
        c=m[j][j]; m[j]=[x/c for x in m[j]]
        for k in range(n):
            if k!=j:
                c=m[k][j]; m[k]=[x-c*y for x,y in zip(m[k],m[j])]
    return [r[n:] for r in m]

def mul(a,b):
    return [[sum(x*b[k][j] for k,x in enumerate(r)) for j in range(len(b[0]))] for r in a]

bi=inv(base); coords=mul(old,bi)
print('octad messages',ma,mb,mc,'blocks',blocks)
print('coefficient denominators',sorted({x.denominator for r in coords for x in r}))
signatures = [sum((int(2*x)%2)<<j for j,x in enumerate(r)) for r in coords]
pivots={}; selected=[]; decompositions=[]
for i,s in enumerate(signatures):
    t=s; combo=0
    for p,(v,c) in sorted(pivots.items(),reverse=True):
        if (t>>p)&1: t^=v; combo^=c
    if t:
        k=len(selected); selected.append(i); combo^=1<<k; pivots[t.bit_length()-1]=(t,combo)
        combo=1<<k
    decompositions.append(combo)
glue=[old[i] for i in selected]
gc=[coords[i] for i in selected]
residual=[[x-sum(((mask>>k)&1)*gc[k][j] for k in range(len(gc))) for j,x in enumerate(r)] for r,mask in zip(coords,decompositions)]
assert all(x.denominator==1 for r in residual for x in r)
base_old=mul(base,inv(old)); assert all(x.denominator==1 for r in base_old for x in r)
assert all((2*x).denominator==1 for r in gc for x in r)
data={'blocks':blocks,'octad_messages':[ma,mb,mc],'e8':e8,'base':base,'glue_indices':selected,'glue':glue,
      'base_in_leech':[[int(x) for x in r] for r in base_old],
      'leech_in_base':[[int(x) for x in r] for r in residual],
      'leech_in_glue':[[int((mask>>k)&1) for k in range(len(gc))] for mask in decompositions],
      'twice_glue_in_base':[[int(2*x) for x in r] for r in gc],
      'base_inverse':[[str(x) for x in r] for r in bi]}
# A left inverse of the twelve glue signatures over F_2 gives integer readouts
# which vanish modulo 8 on the base and take the value 4 on one glue vector.
sigs=[[int(2*x)%2 for x in r] for r in gc]
aug=[r+[int(i==j) for j in range(12)] for i,r in enumerate(sigs)]
pcols=[]; row=0
for col in range(24):
    pivot=next((i for i in range(row,12) if aug[i][col]),None)
    if pivot is None: continue
    aug[row],aug[pivot]=aug[pivot],aug[row]
    for i in range(12):
        if i!=row and aug[i][col]: aug[i]=[a^b for a,b in zip(aug[i],aug[row])]
    pcols.append(col); row+=1
    if row==12: break
forms=[]
for k in range(12):
    q=[sum(8*bi[j][p]*aug[r][24+k] for r,p in enumerate(pcols)) for j in range(24)]
    assert all(x.denominator==1 for x in q)
    forms.append([int(x) for x in q])
assert all(sum(q[j]*v[j] for j in range(24))%8==0 for q in forms for v in base)
assert all(sum(q[j]*v[j] for j in range(24))%8==4*int(k==i) for k,q in enumerate(forms) for i,v in enumerate(glue))
data['readout']=forms

def table(name, a):
    return f'def {name} : List (List ℤ) :=\n  [' + ',\n   '.join(str(r) for r in a) + ']\n\n'
text='''import Mathlib

/-! Concrete integer data for the three-E₈ construction. All certificate identities are
checked in `LeechThreeE8.lean`; the script which found these tables is not trusted. -/

namespace LeechThreeE8

abbrev Vec := Fin 24 → ℤ

'''
for name,key in [('e8Table','e8'),('baseTable','base'),('glueTable','glue'),('baseInLeechTable','base_in_leech'),('leechInBaseTable','leech_in_base'),('leechInGlueTable','leech_in_glue'),('twiceGlueTable','twice_glue_in_base'),('readoutTable','readout')]:
    text+=table(name,data[key])
text+='def coordinateOrder : List Nat := '+str(sum(data['blocks'],[]))+'\n\n'
text+='''def e8Root (i j : Fin 8) : ℤ := (e8Table[i.val]?.getD [])[j.val]?.getD 0
def base (i : Fin 24) : Vec := fun j => (baseTable[i.val]?.getD [])[j.val]?.getD 0
def glue (i : Fin 12) : Vec := fun j => (glueTable[i.val]?.getD [])[j.val]?.getD 0
def baseInLeech (i j : Fin 24) : ℤ := (baseInLeechTable[i.val]?.getD [])[j.val]?.getD 0
def leechInBase (i j : Fin 24) : ℤ := (leechInBaseTable[i.val]?.getD [])[j.val]?.getD 0
def leechInGlue (i : Fin 24) (j : Fin 12) : ℤ := (leechInGlueTable[i.val]?.getD [])[j.val]?.getD 0
def twiceGlue (i : Fin 12) (j : Fin 24) : ℤ := (twiceGlueTable[i.val]?.getD [])[j.val]?.getD 0
def readoutCoeff (i : Fin 12) (j : Fin 24) : ℤ := (readoutTable[i.val]?.getD [])[j.val]?.getD 0

end LeechThreeE8
'''

outputs = {'LeechThreeE8Data.lean': text,
           'docs/three-e8-construction.json': json.dumps(data, indent=2)+'\n'}
for name, contents in outputs.items():
    destination = root / name
    if '--check' in sys.argv:
        assert destination.read_text(encoding='utf-8') == contents, f'Generated data differs: {name}'
    else:
        destination.write_text(contents, encoding='utf-8')
print('PASS: rational construction data and Lean tables agree.' if '--check' in sys.argv else 'Wrote construction witnesses; run Lean to verify them.')
