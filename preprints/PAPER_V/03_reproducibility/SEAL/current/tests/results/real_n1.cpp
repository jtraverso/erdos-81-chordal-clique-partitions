#define main seal_cli_main
#include "../../cpp/seal.cpp"
#undef main
int main(){vector<vector<int>>h{{0,1,2},{0,1}};vector<int>c{1,1};printResult(sealRun(h,c,nullptr,0,1),true);}