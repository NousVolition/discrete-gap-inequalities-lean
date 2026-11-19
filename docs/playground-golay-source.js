const Q = [];
for (let i = 1; i < 23; i++) { const r = (i * i) % 23; if (!Q.includes(r)) Q.push(r); }
const gens = [];
for (let s = 0; s < 23; s++) {
  let w = 0;
  for (const x of Q) w |= 1 << ((x + s) % 23);
  w |= 1 << 23;               // parity bit at position 23 ("infinity"): pattern has 11 ones
  gens.push(w >>> 0);
}
gens.push(0xFFFFFF);          // all-ones word
const basis = [];
for (const g of gens) {
  let v = g;
  for (const b of basis) v = Math.min(v, (v ^ b) >>> 0);
  if (v) { basis.push(v); basis.sort((a, b) => b - a); }
}
let code = [0];
for (const b of basis) code = code.concat(code.map(c => (c ^ b) >>> 0));
const popcount = x => { let n = 0; while (x) { n += x & 1; x >>>= 1; } return n; };
const weights = code.map(popcount);
const octads = code.filter((c, i) => weights[i] === 8);
const dodecads = code.filter((c, i) => weights[i] === 12).length;

// ---------- 2. The 196,560 shortest Leech vectors (scaled by sqrt 8) ----------
const N = 1104 + octads.length * 128 + code.length * 24;
const vecs = new Int8Array(N * 24);
const shellOf = new Uint8Array(N);
let n = 0;
function put(v, shell) { vecs.set(v, n * 24); shellOf[n] = shell; n++; }
// (a) (±4, ±4, 0^22)
for (let i = 0; i < 24; i++) for (let j = i + 1; j < 24; j++)
  for (const a of [-4, 4]) for (const b of [-4, 4]) {
    const v = new Int8Array(24); v[i] = a; v[j] = b; put(v, 0);
  }
// (b) (±2)^8 on an octad, even number of minus signs
for (const o of octads) {
  const idx = [];
  for (let j = 0; j < 24; j++) if ((o >>> j) & 1) idx.push(j);
  for (let m = 0; m < 256; m++) {
    if (popcount(m) % 2) continue;
    const v = new Int8Array(24);
    for (let k = 0; k < 8; k++) v[idx[k]] = ((m >> k) & 1) ? -2 : 2;
    put(v, 1);
  }
}
// (c) (-3, 1^23) with the -3 anywhere, then signs flipped on a Golay codeword
for (let i = 0; i < 24; i++) for (const c of code) {
  const v = new Int8Array(24);
  for (let j = 0; j < 24; j++) {
    const base = j === i ? -3 : 1;
    v[j] = ((c >>> j) & 1) ? -base : base;
  }
  put(v, 2);
}
let allNorm32 = true;
for (let k = 0; k < N && allNorm32; k++) {
  let s = 0;
  for (let j = 0; j < 24; j++) { const x = vecs[k * 24 + j]; s += x * x; }
  if (s !== 32) allNorm32 = false;
}
