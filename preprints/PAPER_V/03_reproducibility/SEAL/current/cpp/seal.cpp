// SEAL and extensions -- C++ port (g++ -std=c++17).
// Authors: Juan Pablo Traverso Gianini. Corrected prepublication N1, 18 October 2026.
// Companion repository artifact; not part of the manuscript, no theorem claims.
// Mirrors python/seal.py deterministically for cross-language validation.
// Covers the four SEAL variants (construction + repair); ILP/LP bounds live
// only in the Python reference. Reads the shared JSON instances.
#include <bits/stdc++.h>
using namespace std;

// ---- tiny JSON extraction for our fixed schema (no spaces in output) ----
static string slurp(const string& p){ ifstream f(p); stringstream ss; ss<<f.rdbuf(); return ss.str(); }
// The fixed-schema extractor below consumes compact JSON. Preserve string
// contents while accepting ordinary pretty-printed instance files as input.
static string compactJson(const string& s){
    string out; bool quoted=false,escaped=false;
    for(char c:s){
        if(quoted){out+=c;if(escaped)escaped=false;else if(c=='\\')escaped=true;else if(c=='"')quoted=false;}
        else if(c=='"'){quoted=true;out+=c;}else if(!isspace(static_cast<unsigned char>(c)))out+=c;
    }
    return out;
}

static vector<vector<int>> parseHosts(const string& s){
    vector<vector<int>> hosts;
    size_t p=s.find("\"hosts\":["); p=s.find('[',p+8); // at outer '['
    int depth=0; vector<int> cur; bool inNum=false; string num;
    for(size_t i=p;i<s.size();++i){
        char c=s[i];
        if(c=='['){ depth++; if(depth==2){cur.clear();} }
        else if(c==']'){
            if(inNum){cur.push_back(stoi(num));num.clear();inNum=false;}
            if(depth==2) hosts.push_back(cur);
            depth--; if(depth==0) break;
        } else if(isdigit(c)||c=='-'){ inNum=true; num+=c; }
        else if(c==','){ if(inNum){cur.push_back(stoi(num));num.clear();inNum=false;} }
    }
    return hosts;
}
static vector<int> parseCaps(const string& s){
    vector<int> caps; size_t k=s.find("\"caps\":["); if(k==string::npos) return caps;
    size_t p=s.find('[',k); string num; bool inNum=false;
    for(size_t i=p+1;i<s.size();++i){ char c=s[i];
        if(c==']'){ if(inNum)caps.push_back(stoi(num)); break; }
        else if(isdigit(c)){inNum=true;num+=c;}
        else if(c==','){ if(inNum){caps.push_back(stoi(num));num.clear();inNum=false;} }
    }
    return caps;
}
static unordered_map<string,double> parseWeights(const string& s){
    unordered_map<string,double> W; size_t k=s.find("\"weights\":{"); if(k==string::npos) return W;
    size_t p=s.find('{',k); size_t end=s.find('}',p);
    size_t i=p+1;
    while(i<end){
        size_t q1=s.find('"',i); if(q1==string::npos||q1>end) break;
        size_t q2=s.find('"',q1+1); string key=s.substr(q1+1,q2-q1-1);
        size_t colon=s.find(':',q2); size_t j=colon+1; string num;
        while(j<s.size() && (isdigit(s[j])||s[j]=='.'||s[j]=='-')){num+=s[j];++j;}
        W[key]=stod(num); i=j;
    }
    return W;
}
static vector<string> parseManifest(const string& s){
    vector<string> v; size_t i=0;
    while(true){ size_t q1=s.find('"',i); if(q1==string::npos) break;
        size_t q2=s.find('"',q1+1); v.push_back(s.substr(q1+1,q2-q1-1)); i=q2+1; }
    return v;
}

static inline string keyOf(int a,int b){ if(a>b) swap(a,b); return to_string(a)+","+to_string(b); }
static inline pair<int,int> parsePair(const string& k){ size_t c=k.find(','); return {stoi(k.substr(0,c)),stoi(k.substr(c+1))}; }

struct Cov {
    vector<string> keys;                 // insertion (discovery) order
    unordered_map<string,vector<int>> m; // key -> covering hosts (insertion order)
};
static Cov buildCov(const vector<vector<int>>& hosts){
    Cov cov;
    for(int j=0;j<(int)hosts.size();++j){
        const auto& N=hosts[j];
        for(size_t a=0;a<N.size();++a) for(size_t b=a+1;b<N.size();++b){
            string k=keyOf(N[a],N[b]);
            auto it=cov.m.find(k);
            if(it==cov.m.end()){ cov.keys.push_back(k); cov.m[k]={j}; }
            else it->second.push_back(j);
        }
    }
    return cov;
}

struct Packing {
    const vector<vector<int>>& hosts; const vector<int>& caps;
    vector<unordered_set<string>> R; vector<unordered_map<int,int>> deg;
    unordered_set<string> used;
    Packing(const vector<vector<int>>& h,const vector<int>& c):hosts(h),caps(c),
        R(h.size()),deg(h.size()){}
    int d(int j,int v)const{ auto it=deg[j].find(v); return it==deg[j].end()?0:it->second; }
    bool canPlace(int j,const string& k)const{ if(used.count(k))return false;
        auto [a,b]=parsePair(k); return d(j,a)<caps[j] && d(j,b)<caps[j]; }
    void place(int j,const string& k){ auto [a,b]=parsePair(k); R[j].insert(k); used.insert(k);
        deg[j][a]++; deg[j][b]++; }
    void remove(int j,const string& k){ auto [a,b]=parsePair(k); R[j].erase(k); used.erase(k);
        deg[j][a]--; deg[j][b]--; }
    double value(const unordered_map<string,double>* W)const{ double s=0;
        for(size_t j=0;j<hosts.size();++j) for(auto& k:R[j]){
            if(W){auto it=W->find(k); s+= it==W->end()?1.0:it->second;} else s+=1; }
        return s; }
    int size()const{ int s=0; for(auto& rj:R) s+=rj.size(); return s; }
    bool relocateInsert(int j,int jp,const string& f,const string& e,double gain){
        if(jp==j || !R[j].count(f) || used.count(e) || gain<=0) return false;
        auto [fa,fb]=parsePair(f); auto [ea,eb]=parsePair(e);
        auto contains=[&](int h,int v){return find(hosts[h].begin(),hosts[h].end(),v)!=hosts[h].end();};
        if(!contains(jp,fa)||!contains(jp,fb)||!contains(j,ea)||!contains(j,eb)) return false;
        remove(j,f);
        if(canPlace(jp,f)){
            place(jp,f);
            if(canPlace(j,e)){place(j,e);return true;}
            remove(jp,f);
        }
        place(j,f); return false;
    }
};

struct Result { double value; int size; int n1_moves; vector<vector<pair<int,int>>> R; };

// mode: 0 standard/psi, 1 weighted, 2 bmatching(caps preset). construct: 0 scarcity,1 hostmatch
static Result sealRun(const vector<vector<int>>& hosts,const vector<int>& caps,
                      const unordered_map<string,double>* W,int mode,int construct){
    Cov cov=buildCov(hosts);
    Packing P(hosts,caps);
    int n1Moves=0;

    if(construct==1){ // hostmatch
        vector<int> order(hosts.size()); iota(order.begin(),order.end(),0);
        sort(order.begin(),order.end(),[&](int i,int j){
            if(hosts[i].size()!=hosts[j].size()) return hosts[i].size()>hosts[j].size();
            return i<j; });
        for(int j:order){ const auto& N=hosts[j];
            for(size_t a=0;a<N.size();++a) for(size_t b=a+1;b<N.size();++b){
                string k=keyOf(N[a],N[b]); if(P.canPlace(j,k)) P.place(j,k); } }
    } else {
        vector<string> keys=cov.keys;
        if(mode==1) stable_sort(keys.begin(),keys.end(),[&](const string&x,const string&y){
            double wx=W->count(x)?W->at(x):1, wy=W->count(y)?W->at(y):1;
            if(wx!=wy) return wx>wy; return cov.m[x].size()<cov.m[y].size(); });
        else stable_sort(keys.begin(),keys.end(),[&](const string&x,const string&y){
            return cov.m[x].size()<cov.m[y].size(); });
        for(auto& k:keys){ if(P.used.count(k))continue;
            for(int j:cov.m[k]) if(P.canPlace(j,k)){ P.place(j,k); break; } }
    }

    bool improved=true;
    while(improved){ improved=false;
        for(auto& k:cov.keys){ if(P.used.count(k))continue;
            for(int j:cov.m[k]) if(P.canPlace(j,k)){ P.place(j,k); improved=true; break; } }
        for(auto& e:cov.keys){ if(P.used.count(e))continue;
            auto [a,b]=parsePair(e);
            for(int j:cov.m[e]){ if(P.used.count(e))break;
                vector<string> blockers;
                for(auto& f:P.R[j]){ auto [x,y]=parsePair(f); if(x==a||x==b||y==a||y==b) blockers.push_back(f); }
                sort(blockers.begin(),blockers.end(),[](const string&p,const string&q){
                    auto pp=parsePair(p),qq=parsePair(q); return pp<qq; });
                for(auto& f:blockers){ bool moved=false;
                    for(int jp:cov.m[f]){ if(jp==j)continue;
                        double gain=W && W->count(e)?W->at(e):1;
                        if(P.relocateInsert(j,jp,f,e,gain)){n1Moves++;moved=true;break;} }
                    if(moved){improved=true;break;} }
                if(P.used.count(e))break;
            } }
    }
    Result out{mode==1 ? P.value(W) : (double)P.size(),P.size(),n1Moves,{}};
    for(auto& rj:P.R){ vector<pair<int,int>> pairs; for(auto& k:rj)pairs.push_back(parsePair(k));
        sort(pairs.begin(),pairs.end());out.R.push_back(pairs); }
    return out;
}

static Result sealBest(const vector<vector<int>>& hosts,const vector<int>& caps,
                       const unordered_map<string,double>* W,int mode){
    Result a=sealRun(hosts,caps,W,mode,0), b=sealRun(hosts,caps,W,mode,1);
    return b.value>a.value ? b:a;
}

static void printResult(const Result& r,bool physical){
    if(!physical){cout<<r.value;return;}
    cout<<"{\"value\":"<<setprecision(15)<<r.value<<",\"size\":"<<r.size<<",\"n1_moves\":"<<r.n1_moves<<",\"R\":[";
    for(size_t j=0;j<r.R.size();j++){cout<<(j?",":"")<<"[";
        for(size_t k=0;k<r.R[j].size();k++)cout<<(k?",":"")<<"["<<r.R[j][k].first<<","<<r.R[j][k].second<<"]";
        cout<<"]";} cout<<"]}";
}

int main(int argc,char** argv){
    string base = argc>1? argv[1] : "../instances";
    bool physical=argc>2 && string(argv[2])=="--packings";
    vector<string> manifest=parseManifest(slurp(base+"/manifest.json"));
    cout<<"{";
    for(size_t idx=0;idx<manifest.size();++idx){
        string name=manifest[idx];
        string s=compactJson(slurp(base+"/"+name+".json"));
        auto hosts=parseHosts(s); auto caps=parseCaps(s); auto W=parseWeights(s);
        vector<int> ones(hosts.size(),1);
        Result st=sealBest(hosts,ones,nullptr,0), wt=sealBest(hosts,ones,&W,1), bm=sealBest(hosts,caps,nullptr,2);
        cout<<(idx?",":"")<<"\""<<name<<"\":{\"standard\":";printResult(st,physical);
        cout<<",\"weighted\":";printResult(wt,physical);cout<<",\"bmatching\":";printResult(bm,physical);cout<<"}";
    }
    cout<<"}"<<endl;
    return 0;
}
