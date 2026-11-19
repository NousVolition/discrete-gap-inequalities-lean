// External source replay. This is not a Lean proof of JavaScript execution.
'use strict';
const fs = require('node:fs'), path = require('node:path'), vm = require('node:vm');
const crypto = require('node:crypto'), assert = require('node:assert/strict');
const root = path.resolve(__dirname, '..');
const read = file => fs.readFileSync(file, 'utf8').replace(/\r\n/g, '\n');
const sha = text => crypto.createHash('sha256').update(text).digest('hex');
const archived = read(path.join(root, 'docs/playground-golay-source.js'));
const provenance = JSON.parse(read(path.join(root, 'docs/playground-golay-source.json')));
assert.equal(sha(archived), provenance.source_slice_sha256);
let source = archived;
if (process.argv[2]) {
  const html = read(path.resolve(process.argv[2]));
  const matches = [...html.matchAll(/<template id="page-src-leech">([\s\S]*?)<\/template>/g)];
  assert.equal(matches.length, 1);
  const tab = matches[0][1], start = tab.indexOf('const Q = [];');
  const end = tab.indexOf("document.getElementById('sTotal')", start);
  assert(start >= 0 && end > start);
  source = tab.slice(start, end);
  assert.equal(source, archived, 'The page generator/vector source changed; review before reusing this certificate.');
}
const result = new vm.Script(source + '\n({Q, gens, basis, code, octads, dodecads, vecs, shellOf, n, N, allNorm32});')
  .runInNewContext({}, {timeout: 15000});
const formalSource = read(path.join(root, 'PlaygroundGolay.lean'));
function arrayAfter(name) {
  const match = formalSource.match(new RegExp('def ' + name + '[\\s\\S]*?#\\[([^\\]]+)\\]'));
  assert(match, name); return match[1].split(',').map(Number);
}
const basis = arrayAfter('basisMasks'), permutation = arrayAfter('coordinateMap');
const inverse = arrayAfter('inverseMap'), forward = arrayAfter('forwardMessage'), reverse = arrayAfter('reverseMessage');
assert.deepEqual(Array.from(result.basis), basis);
assert.equal(new Set(permutation).size, 24);
for (let i = 0; i < 24; i++) assert.equal(inverse[permutation[i]], i);
const matrixSource = read(path.join(root, 'GolayMatrixDistance.lean'));
const rows = [...matrixSource.matchAll(/=>\s*#\[([^\]]+)\]/g)].map(m => m[1].split(',').map(x => x.trim() === 'true'));
assert.equal(rows.length, 12); assert(rows.every(r => r.length === 12));
const masks = rows.map((row, i) => row.reduce((m,b,j) => b ? m | (1 << (12+j)) : m, 1 << i));
const encode = (bs, m) => bs.reduce((w,b,i) => (m >>> i) & 1 ? w ^ b : w, 0);
const permute = (w,p) => p.reduce((v,j,i) => v | (((w >>> i) & 1) << j), 0);
for (let i=0; i<12; i++) {
  assert.equal(permute(basis[i],permutation),encode(masks,forward[i]));
  assert.equal(permute(masks[i],inverse),encode(basis,reverse[i]));
}
const formalCode = Array.from({length:4096}, (_,m) => encode(masks,m));
const formalSet = new Set(formalCode), playSet = new Set(result.code);
assert.equal(formalSet.size,4096); assert.equal(playSet.size,4096);
for (const w of playSet) assert(formalSet.has(permute(w,permutation)));
const popcount = w => { let n=0; while(w) { n+=w&1; w>>>=1; } return n; };
const distribution = {};
for (const w of playSet) { const n=popcount(w); distribution[n]=(distribution[n]||0)+1; }
assert.deepEqual(distribution,{0:1,8:759,12:2576,16:759,24:1});
const vectors = new Set(), shells=[0,0,0];
const mod = (x,n) => (x%n+n)%n;
assert.equal(result.n,196560); assert.equal(result.N,result.n); assert(result.allNorm32);
for (let k=0; k<result.n; k++) {
  const v = Array.from(result.vecs.slice(24*k,24*(k+1)));
  let sum=0, norm=0; const residues=[0,0,0,0], parity=mod(v[0],2);
  for (let i=0; i<24; i++) {
    assert.equal(mod(v[i],2),parity); sum+=v[i]; norm+=v[i]*v[i];
    residues[mod(v[i],4)] |= 1 << permutation[i];
  }
  assert.equal(norm,32); assert.equal(mod(sum,8),4*parity);
  for (const r of residues) assert(formalSet.has(r));
  vectors.add(v.join(',')); shells[result.shellOf[k]]++;
}
assert.equal(vectors.size,196560); assert.deepEqual(shells,[1104,97152,98304]);
console.log(JSON.stringify({status:'PASS', evidence_kind:'External JavaScript source replay; not a Lean execution theorem',
  source_commit:provenance.commit, source_slice_sha256:sha(source),
  checked_current_page_source:Boolean(process.argv[2]),
  formal_source_sha256:{'PlaygroundGolay.lean':sha(formalSource),'GolayMatrixDistance.lean':sha(matrixSource)},
  playground_to_lean_coordinates:permutation, playground_basis:basis, forward_messages:forward, reverse_messages:reverse,
  codewords:playSet.size, mapped_codewords:4096, weight_distribution:distribution,
  vector_families:shells, distinct_vectors:vectors.size, all_squared_norms:32,
  mapped_vectors_satisfying_InLeech_rule:result.n,
  scope:'Replays the archived integer generator and vector loops, compares both bases with the Lean source, and checks all outputs. Browser rendering, projection and animation are not checked.'
},null,2));
