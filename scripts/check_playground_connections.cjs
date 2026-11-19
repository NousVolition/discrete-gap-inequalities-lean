// Reproduce the bounded source/computation review documented in docs/playground-connections.md.
// No browser controls, fluid simulation, Lean compiler, or proof-status changes are involved.
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const vm = require('node:vm');
const assert = require('node:assert/strict');

if (process.argv.length !== 3) throw Error('Usage: node scripts/check_playground_connections.cjs INDEX_HTML');
const bytes = fs.readFileSync(process.argv[2]);
const html = bytes.toString('utf8').replace(/\r\n/g, '\n');
const sha = x => crypto.createHash('sha256').update(x).digest('hex');
const expected = 'b5eb5238b1aef886b42dc3a342540ac150aa8eb1398311afdec2a74475a40fc2';
assert.equal(sha(html), expected, 'Use index.html from the pinned playground revision');
function between(text, begin, end) {
  const i = text.indexOf(begin);
  assert(i >= 0 && text.indexOf(begin, i + begin.length) < 0, `Non-unique start: ${begin}`);
  const j = text.indexOf(end, i + begin.length);
  assert(j > i, `Missing end: ${end}`);
  return text.slice(i, j);
}
function run(code) {
  const context = vm.createContext({});
  return new vm.Script(code).runInContext(context, { timeout: 5000 });
}

// Reuse the HUD's actual edge-counting and logarithmic-bound arithmetic, stopping before rendering.
const hud = between(html, 'function updateCubeHUD() {', "  document.getElementById('hudM')");
const cube = run(`const cubeDim=3; const selectedSet=new Set([0,1,2]);
${hud} return {m,internal,boundary,maxBound}; } updateCubeHUD();`);
assert.equal(cube.internal, 2);
let exactMaximum = 0, setsChecked = 0;
for (let mask = 0; mask < 256; mask++) {
  if (mask.toString(2).replace(/0/g, '').length !== 3) continue;
  let edges = 0;
  for (let u = 0; u < 8; u++) for (let b = 0; b < 3; b++) {
    const v = u ^ (1 << b);
    if (u < v && ((mask >> u) & 1) && ((mask >> v) & 1)) edges++;
  }
  exactMaximum = Math.max(exactMaximum, edges); setsChecked++;
}
assert.equal(exactMaximum, 2);
assert.equal(setsChecked, 56);
assert.equal(cube.boundary, 5);
assert(cube.maxBound > exactMaximum);

// The cycle update as implemented, with only its numerical inputs supplied here.
const cycleCode = between(html, '  // 2. Cycle Laplacian (Periodic)', '  // 3. 3D Cube Laplacian');
const cycle = [1, 4, 10].map(speed => {
  const n = 6, dt = speed * .004;
  const input = Array.from({length:n}, (_,j) => Math.cos(2*Math.PI*j/n));
  const output = run(`const N_1D=6, dt=${dt}; let uCycle=${JSON.stringify(input)};
${cycleCode}\nuCycle;`);
  const gap = 2-2*Math.cos(2*Math.PI/n), factor = 1-dt*gap;
  const error = Math.max(...output.map((v,j) => Math.abs(v-factor*input[j])));
  assert(error < 1e-12 && dt >= 0 && dt <= .25);
  return {speed,dt,gap,factor,maximum_wave_update_difference:error};
});

// Direction-ring and centered Wirtinger calculations from the Unit Distances page.
const unitCode = between(html, '  function ringOf(k) {', '  window.unitDistances =');
const unit = run(`${unitCode}
[1,2,5,25,65].map(k => { const ring=ringOf(k);
 return {k,directions:ring.length,x:wirtinger(ring.map(p=>p[0])),y:wirtinger(ring.map(p=>p[1]))}; });`);
for (const r of unit) for (const axis of ['x','y']) assert(r[axis].ratio >= 1-1e-12);

// The cipher page exposes this pure gauge independently of its annealing heuristic.
const gaugeCode = between(html, 'function wirtingerGauge(values) {', '// One animation frame of work:');
const cipher = run(`${gaugeCode}
({sharp:wirtingerSelfTest(),constant:wirtingerGauge(Array(8).fill(5))});`);
assert(cipher.sharp.every(r => r.ok));
assert(cipher.constant.flat && Number.isNaN(cipher.constant.W));
const certCode = between(html, 'function exportCertificate(cipherText, symbols, key) {', '/* ---------- Mandala view helpers ---------- */');
const certificate = run(`${certCode}
const cert=exportCertificate('#@@#',['#','@'],[0,1]);
({decoded:cert.decoded,valid:checkCertificate(cert).pass,
 tampered:checkCertificate({...cert,decoded:'AABA'}).pass,
 exported_theorems:(leanCertificate(cert).match(/^theorem /gm)||[]).length});`);
assert.equal(certificate.decoded,'ABBA');
assert(certificate.valid && !certificate.tampered && certificate.exported_theorems===2);

// Compare finite codeword enumerations; this is external integer arithmetic, not Lean verification.
const leechCode = between(html, '// ---------- 1. The extended Golay code', '// ---------- 2. The 196,560 shortest Leech vectors');
const leech = run(`${leechCode}\n({code,basisSize:basis.length});`);
const leanFile = fs.readFileSync(path.resolve(__dirname,'../GolayMatrixDistance.lean'),'utf8');
const parity = between(leanFile, 'def golayParityRow', '/-- Entry (i, j)');
const rows = [...parity.matchAll(/#\[([^\]]+)\]/g)].map(m => [...m[1].matchAll(/true|false/g)].map(v=>v[0]==='true'));
assert(rows.length===12 && rows.every(r=>r.length===12));
const generators = rows.map((r,i)=>r.reduce((mask,v,j)=>v ? mask|(1<<(j+12)) : mask, 1<<i));
let leanWords = [0];
for (const g of generators) leanWords = leanWords.concat(leanWords.map(w=>w^g));
const histogram = words => words.reduce((a,w)=>{
  const weight=w.toString(2).replace(/0/g,'').length;
  a[weight]=(a[weight]||0)+1; return a;
},{});
const expectedWeights = {0:1,8:759,12:2576,16:759,24:1};
assert.deepEqual(histogram(leech.code),expectedWeights);
assert.deepEqual(histogram(leanWords),expectedWeights);
assert.equal(new Set(leech.code).size,4096);
assert.equal(leech.basisSize,12);
const leanSet = new Set(leanWords);
assert.equal(leanSet.size,4096);
const intersection = leech.code.filter(w=>leanSet.has(w)).length;

assert(html.includes('Gap &lambda;₂ = 0.268'));
const report = {
  status:'PASS_SOURCE_AND_NUMERICAL_CHECKS_ONLY',
  source_commit:'03ef852cce4ae0d2cdb2319c413b6755bcf6e593',
  source_url:'https://github.com/NousVolition/sparkle-sand-playground/blob/03ef852cce4ae0d2cdb2319c413b6755bcf6e593/index.html',
  normalized_html_sha256:sha(html),
  golay_lean_sha256:sha(leanFile.replace(/\r\n/g,'\n')),
  path:{points:6,displayed_gap:.268,proved_Poincare_constant:2/(6*5)},
  cube:{...cube,exact_maximum:exactMaximum,three_vertex_sets_checked:setsChecked,
    displayed_shortfall:cube.maxBound-cube.internal,
    finding:'The logarithmic upper bound is not the exact fixed-cardinality maximum.'},
  cycle_heat:cycle,
  unit_distance_rings:unit,
  cipher_gauge:cipher,
  cipher_certificate:{...certificate,lean_compilation:'not run; not included in the 535 audited statements'},
  golay:{playground_basis_size:leech.basisSize,codewords:leech.code.length,
    weight_distribution:histogram(leech.code),same_coordinate_codewords_in_common:intersection,
    identical_codeword_sets:intersection===4096,
    scope:'No coordinate-equivalence or Leech-lattice theorem is proved by this check.'},
  limitations:['No live controls were exercised.','Floating-point checks are not proofs.',
    'No new Lean statements or browser-to-Lean equivalence certificates were added.',
    'No cipher correctness, solver convergence, or uniqueness claim is checked.']
};
process.stdout.write(JSON.stringify(report,null,2)+'\n');
