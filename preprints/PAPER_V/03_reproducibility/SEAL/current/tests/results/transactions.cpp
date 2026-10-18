#define main seal_cli_main
#include "../../cpp/seal.cpp"
#undef main
int main(){cout<<"[";
{vector<vector<int>> hosts={{0,1,2},{0,1}};vector<int> caps={1,1};Packing p(hosts,caps);
p.place(0,"0,1");
bool ok=p.relocateInsert(0,1,"0,1","0,2",1);
Result result{0,p.size(),0,{}};for(auto&r:p.R){vector<pair<int,int>> pairs;for(auto&e:r)pairs.push_back(parsePair(e));sort(pairs.begin(),pairs.end());result.R.push_back(pairs);}
cout<<"{\"name\":\"cap1_improves\",\"accepted\":"<<(ok?"true":"false")<<",\"output\":";printResult(result,true);cout<<"}";}
{vector<vector<int>> hosts={{0,1,2},{0,1}};vector<int> caps={1,1};Packing p(hosts,caps);
p.place(0,"0,1");
bool ok=p.relocateInsert(0,1,"0,1","0,2",0.5);
Result result{0,p.size(),0,{}};for(auto&r:p.R){vector<pair<int,int>> pairs;for(auto&e:r)pairs.push_back(parsePair(e));sort(pairs.begin(),pairs.end());result.R.push_back(pairs);}
cout<<",{\"name\":\"weighted_positive\",\"accepted\":"<<(ok?"true":"false")<<",\"output\":";printResult(result,true);cout<<"}";}
{vector<vector<int>> hosts={{0,1,2},{0,1}};vector<int> caps={1,1};Packing p(hosts,caps);
p.place(0,"0,1");
bool ok=p.relocateInsert(0,1,"0,1","0,2",0);
Result result{0,p.size(),0,{}};for(auto&r:p.R){vector<pair<int,int>> pairs;for(auto&e:r)pairs.push_back(parsePair(e));sort(pairs.begin(),pairs.end());result.R.push_back(pairs);}
cout<<",{\"name\":\"zero_gain_rejected\",\"accepted\":"<<(ok?"true":"false")<<",\"output\":";printResult(result,true);cout<<"}";}
{vector<vector<int>> hosts={{0,1,2},{0,1}};vector<int> caps={1,1};Packing p(hosts,caps);
p.place(0,"0,1");
bool ok=p.relocateInsert(0,1,"0,1","0,2",-1);
Result result{0,p.size(),0,{}};for(auto&r:p.R){vector<pair<int,int>> pairs;for(auto&e:r)pairs.push_back(parsePair(e));sort(pairs.begin(),pairs.end());result.R.push_back(pairs);}
cout<<",{\"name\":\"negative_gain_rejected\",\"accepted\":"<<(ok?"true":"false")<<",\"output\":";printResult(result,true);cout<<"}";}
{vector<vector<int>> hosts={{0,1,2},{0,1,3}};vector<int> caps={1,1};Packing p(hosts,caps);
p.place(0,"0,1");
p.place(1,"0,3");
bool ok=p.relocateInsert(0,1,"0,1","0,2",1);
Result result{0,p.size(),0,{}};for(auto&r:p.R){vector<pair<int,int>> pairs;for(auto&e:r)pairs.push_back(parsePair(e));sort(pairs.begin(),pairs.end());result.R.push_back(pairs);}
cout<<",{\"name\":\"destination_full_rollback\",\"accepted\":"<<(ok?"true":"false")<<",\"output\":";printResult(result,true);cout<<"}";}
{vector<vector<int>> hosts={{0,1,2,3},{0,1}};vector<int> caps={1,1};Packing p(hosts,caps);
p.place(0,"0,1");
p.place(0,"2,3");
bool ok=p.relocateInsert(0,1,"0,1","0,2",1);
Result result{0,p.size(),0,{}};for(auto&r:p.R){vector<pair<int,int>> pairs;for(auto&e:r)pairs.push_back(parsePair(e));sort(pairs.begin(),pairs.end());result.R.push_back(pairs);}
cout<<",{\"name\":\"target_blocked_rollback\",\"accepted\":"<<(ok?"true":"false")<<",\"output\":";printResult(result,true);cout<<"}";}
{vector<vector<int>> hosts={{0,1,2,3,4},{0,1}};vector<int> caps={2,2};Packing p(hosts,caps);
p.place(0,"0,1");
p.place(0,"0,3");
p.place(0,"2,4");
bool ok=p.relocateInsert(0,1,"0,1","0,2",1);
Result result{0,p.size(),0,{}};for(auto&r:p.R){vector<pair<int,int>> pairs;for(auto&e:r)pairs.push_back(parsePair(e));sort(pairs.begin(),pairs.end());result.R.push_back(pairs);}
cout<<",{\"name\":\"cap2_improves\",\"accepted\":"<<(ok?"true":"false")<<",\"output\":";printResult(result,true);cout<<"}";}
{vector<vector<int>> hosts={{0,1,2,3,4},{0,1}};vector<int> caps={2,2};Packing p(hosts,caps);
p.place(0,"0,1");
p.place(0,"2,3");
p.place(0,"2,4");
bool ok=p.relocateInsert(0,1,"0,1","0,2",1);
Result result{0,p.size(),0,{}};for(auto&r:p.R){vector<pair<int,int>> pairs;for(auto&e:r)pairs.push_back(parsePair(e));sort(pairs.begin(),pairs.end());result.R.push_back(pairs);}
cout<<",{\"name\":\"cap2_target_full_rollback\",\"accepted\":"<<(ok?"true":"false")<<",\"output\":";printResult(result,true);cout<<"}";}
{vector<vector<int>> hosts={{0,1,2},{0,3}};vector<int> caps={1,1};Packing p(hosts,caps);
p.place(0,"0,1");
bool ok=p.relocateInsert(0,1,"0,1","0,2",1);
Result result{0,p.size(),0,{}};for(auto&r:p.R){vector<pair<int,int>> pairs;for(auto&e:r)pairs.push_back(parsePair(e));sort(pairs.begin(),pairs.end());result.R.push_back(pairs);}
cout<<",{\"name\":\"nonhost_destination_rejected\",\"accepted\":"<<(ok?"true":"false")<<",\"output\":";printResult(result,true);cout<<"}";}
cout<<"]";return 0;}