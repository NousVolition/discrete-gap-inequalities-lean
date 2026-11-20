// External integer replay of the actual playground source; this does not run Lean.
'use strict';
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict'),crypto=require('node:crypto');
const root=path.resolve(__dirname,'..'),play=path.resolve(process.argv[2]||'../sparkle-sand-playground');
const read=p=>fs.readFileSync(p,'utf8').replace(/\r\n/g,'\n');
const sha=s=>crypto.createHash('sha256').update(s).digest('hex');
const formal=read(path.join(root,'LeechThreeE8Data.lean')), data=JSON.parse(read(path.join(root,'docs/three-e8-construction.json')));
for(const [name,key] of Object.entries({e8Table:'e8',baseTable:'base',glueTable:'glue',baseInLeechTable:'base_in_leech',leechInBaseTable:'leech_in_base',leechInGlueTable:'leech_in_glue',twiceGlueTable:'twice_glue_in_base',readoutTable:'readout'})) {
  const match=formal.match(new RegExp('def '+name+' : List \\(List ℤ\\) :=\\n([\\s\\S]*?)\\n\\n'));
  assert(match,name);assert.deepEqual(JSON.parse(match[1]),data[key]);
}
const html=read(path.join(play,'index.html')),tab=html.match(/<template id="page-src-leech">([\s\S]*?)<\/template>/)[1];
const source=tab.slice(tab.indexOf('const Q = [];'),tab.indexOf("document.getElementById('sTotal')"));
assert.equal(source,read(path.join(root,'docs/playground-golay-source.js')),'The existing vector generator changed.');
const generated=new vm.Script(source+'\n({vecs,N,n,shellOf});').runInNewContext({}, {timeout:15000});
const asset=read(path.join(play,'leech-three-e8-data.js')),implementation=read(path.join(play,'leech-three-e8.js'));
const sandbox={};sandbox.window=sandbox;vm.createContext(sandbox);vm.runInContext(asset,sandbox);vm.runInContext(implementation,sandbox);
const api=sandbox.LeechThreeE8,browser=JSON.parse(JSON.stringify(sandbox.LEECH_THREE_E8_DATA));
for(const key of ['blocks','e8','glue','readout'])assert.deepEqual(browser[key],data[key]);
const p=read(path.join(root,'PlaygroundGolay.lean')).match(/def inverseMap[\s\S]*?#\[([^\]]+)\]/)[1].split(',').map(Number);
assert.deepEqual(browser.leanToPlay,p);
for(let i=0;i<24;i++)for(let j=0;j<24;j++)assert.equal(data.base[i].reduce((s,v,k)=>s+v*browser.inverseTimes8[k][j],0),8*Number(i===j));
const distinct=new Set();
for(let mask=0;mask<4096;mask++){const g=api.shift(mask);assert.equal(api.label(g),mask);distinct.add(api.label(g));}
const counts=Array(4096).fill(0),energyPatterns={};let checked=0;
for(let k=0;k<generated.N;k++) {
  const v=generated.vecs.subarray(k*24,(k+1)*24),d=api.decompose(v);
  assert(d.coefficients.every(Number.isInteger));
  for(let j=0;j<24;j++)assert.equal(d.shift[j]+d.coefficients.reduce((s,c,i)=>s+c*data.base[i][j],0),d.v[j]);
  const energies=d.blocks.map(b=>b.reduce((s,x)=>s+x*x,0));assert.equal(energies.reduce((a,b)=>a+b,0),32);
  counts[d.mask]++;const key=[...energies].sort((a,b)=>a-b).join('+');energyPatterns[key]=(energyPatterns[key]||0)+1;checked++;
}
const roots=api.roots();assert.equal(roots.length,240);assert.equal(new Set(roots.map(x=>x.join(','))).size,240);
const inverse8=browser.inverseTimes8;
for(let block=0;block<3;block++)for(const r of roots){
  const v=Array(24).fill(0);data.blocks[block].forEach((j,i)=>v[j]=r[i]);assert.equal(api.label(v),0);
  for(let i=0;i<24;i++)assert(v.reduce((s,x,j)=>s+x*inverse8[j][i],0)%8===0);
  assert.equal(v.reduce((s,x)=>s+x*x,0),32);
}
const distribution={};for(const n of counts)distribution[n]=(distribution[n]||0)+1;
assert.equal(checked,196560);assert.equal(counts[0],720);
console.log(JSON.stringify({status:'PASS',evidence_kind:'External integer JavaScript replay; not a Lean proof of browser execution',
  generator_sha256:sha(source),formal_data_sha256:sha(formal),construction_json_sha256:sha(read(path.join(root,'docs/three-e8-construction.json'))),
  browser_source_sha256:{'leech-three-e8-data.js':sha(asset),'leech-three-e8.js:integer-prefix-before-mount':sha(implementation.slice(0,implementation.indexOf('  function mount(')))},
  distinct_glue_labels:distinct.size,vectors_reconstructed_in_three_e8:checked,all_squared_lengths:32,
  roots_per_e8_block:roots.length,base_coset_shortest_vectors:counts[0],coset_size_distribution:distribution,component_energy_patterns:energyPatterns,
  scope:'Compares browser tables with the Lean data, checks the inverse matrix, all 4096 glue readouts and all 196560 vector decompositions. This does not check rendering or claim these JavaScript checks are Lean proofs.'},null,2));
