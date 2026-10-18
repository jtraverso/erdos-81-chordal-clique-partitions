const fs=require('fs'),{Packing,normalize,seal}=require('../../js/seal.js');
const cases=JSON.parse(fs.readFileSync(process.argv[2]));
const out=cases.map(c=>{const p=new Packing(normalize(c.hosts),c.caps);
for(const [j,e] of c.initial)p.place(j,e.join(','));
const accepted=p.relocateInsert(0,1,c.f.join(','),c.e.join(','),c.gain);
return {name:c.name,accepted,R:p.R.map(r=>[...r].map(e=>e.split(',').map(Number)).sort((a,b)=>a[0]-b[0]||a[1]-b[1]))};});
console.log(JSON.stringify(out));