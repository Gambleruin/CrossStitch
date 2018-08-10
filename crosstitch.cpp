#include<tuple>
#include<cmath>
#include<queue>
#include<stdio.h>
#include<iostream>
#include<vector>
#include<algorithm>
#include<string>
#include<string.h>
using namespace std;

typedef long long LL;
typedef vector<int> VI;

#define REP(i,n) for(int i=0, i##_len=(n); i<i##_len; ++i)
#define EACH(i,c) for(__typeof((c).begin()) i=(c).begin(),i##_end=(c).end();i!=i##_end;++i)

#ifdef LOCAL
#define eprintf(...) fprintf(stderr, __VA_ARGS__)
#else
#define NDEBUG
#define eprintf(...) 0
#endif
#include<assert.h>

template<class T> inline void amin(T &x, const T &y) { if (y<x) x=y; }
template<class T> inline void amax(T &x, const T &y) { if (x<y) x=y; }
template<class Iter> void rprintf(const char *fmt, Iter begin, Iter end) {
    for (bool sp=0; begin!=end; ++begin) { if (sp) putchar(' '); else sp = true; printf(fmt, *begin); }
    putchar('\n');
}
inline LL pow2(int i) { return 1LL<<i; };

const int dy[6] = { 0, 1, 0, 1, 0, 1 };
const int dx[6] = { 0, 1, 1, 0, 0, 1 };
const int adj_d[4][4] = {
    { 2, 3, 1 },
    { 2, 3, 0 },
    { 0, 1, 3 },
    { 0, 1, 2 }
};

const double INF = 1e60;

struct UnionFind {
    int n, cc, *u;
    UnionFind() : n(0), cc(0), u(NULL) {}
    UnionFind(int n_) : n(n_), cc(n_) {
    u = new int[n_];
    memset(u, -1, sizeof (int) * n);
    }
    UnionFind(const UnionFind &y) : n(y.n), cc(y.cc) {
    u = new int[y.n];
    memcpy(u, y.u, sizeof (int) * n);
    }
    ~UnionFind() {
    delete[] u; u = NULL;
    n = cc = 0;
    }
    friend void swap(UnionFind &x, UnionFind &y) {
    swap(x.n, y.n); swap(x.cc, y.cc); swap(x.u, y.u);
    }
    UnionFind& operator=(UnionFind y) { 
    swap(*this, y);
    return *this;
    }
    int root(int x) {
    int y = x, t;
    while (u[y] >= 0) y = u[y];
    while (x != y) { t = u[x]; u[x] = y; x = t; }
    return y;
    }
    bool link(int x, int y) {
    x = root(x); y = root(y);
    if (x == y) return false;
    if (u[y] < u[x]) swap(x, y);
    u[x] += u[y]; u[y] = x; cc--;
    return true;
    }
    bool same(int x, int y) { return root(x) == root(y); }
    int size(int x) { return -u[root(x)]; }
    int count() { return cc; }
};

const int MAXN = 101;
const int MAXNN = MAXN * MAXN;

vector<string> F;
int N;
int R[MAXNN], C[MAXNN];
int stop;

vector<string> ret;
double cost[MAXNN];
bool use[MAXNN];
bool strong[MAXNN];
int par[MAXNN];
VI G[MAXNN];
VI ord;

int sq(int x) { return x * x; }
double dist(int i, int j) { return sqrt(sq(R[i] - R[j]) + sq(C[i] - C[j])); }

void findPosition(char color) {
    stop = 0;
    REP (r, N) REP (c, N) if (F[r][c] == color) {
    R[stop] = r;
    C[stop] = c;
    stop++;
    }

    if (stop == 0) return;

    ret.push_back(string(1, color));
}

int deg[MAXNN];
vector<pair<float, unsigned> > edges;

void setOrdFromGraph() {
    int v = 0, p;
    REP (i, stop) if (deg[i] == 1) { v = i; break; }
    p = v;
    ord.clear();
    ord.reserve(stop);
    REP (i, stop) {
    ord.push_back(v);
    EACH (e, G[v]) if (*e != p) {
        p = v;
        v = *e;
        break;
    }
    }
}

char dp_buf[1<<28]; // 256_000_000

void refineOrd() {
    bool update = false;
    do {
    update = false;
    REP (i, stop-2) for (int j=i+2; j<stop-1; j++) {
        if (dist(ord[i], ord[i+1]) + dist(ord[j], ord[j+1]) >
            dist(ord[i], ord[j]) + dist(ord[j+1], ord[i+1])) {
        reverse(ord.begin() + i + 1, ord.begin() + j + 1);
        update = true;
        }
    }
    } while (update) ;
}

void buildPathDp() {
    ord.clear();
    if (stop == 0) return;
    if (stop == 1) {
    ord.push_back(0);
    return;
    }

    REP (i, stop) G[i].clear();
    UnionFind U(stop);
    memset(deg, 0, sizeof (int) * stop);
    REP (i, stop-1) {
    if (R[i] == R[i+1] &&  abs(C[i] - C[i+1]) <= 2) {
        U.link(i, i+1);
        G[i].push_back(i+1);
        G[i+1].push_back(i);
        deg[i]++;
        deg[i+1]++;
    }
    }

    edges.clear();
    REP (j, stop) if (deg[j] <= 1) REP (i, j) if (deg[i] <= 1) { 
    if (!U.same(i, j))
        edges.emplace_back(dist(i, j), i * stop + j);
    }
    sort(edges.begin(), edges.end());

    const int DP_MAX = 16;
    REP (i, edges.size()) {
    if (U.count() <= DP_MAX)  break;

    int a = edges[i].second / stop;
    int b = edges[i].second % stop;
    if (deg[a] < 2 && deg[b] < 2 && !U.same(a, b)) {
        G[a].push_back(b);
        G[b].push_back(a);
        deg[a]++; deg[b]++;
        U.link(a, b);
    }
    }
    
    int size = U.count();
    if (size > 1) {
    // 8 * (1<<18) * 18 * 2
    double (*dp)[DP_MAX * 2] = (double (*)[DP_MAX*2]) dp_buf;
    int (*pre)[DP_MAX * 2] = (int (*)[DP_MAX*2]) (dp_buf + (1<<27));
    REP (s, pow2(size)) REP (i, DP_MAX*2) {
        dp[s][i] = INF;
    }
    assert((void*)&dp[pow2(DP_MAX)-1][DP_MAX*2] < (void*)&pre[0][0]);

    memset(pre, -1, sizeof (int) * pow2(size) * DP_MAX * 2);

    int pos = 0;
    static pair<int, int> name[DP_MAX * 2];
    REP (i, stop) {
        if (deg[i] == 0) {
        name[pos++] = make_pair(i, i);
        name[pos++] = make_pair(i, i);
        } else if (deg[i] == 1) {
        name[pos++] = make_pair(U.root(i), i);
        }
    }

    assert(pos == size * 2);
    sort(name, name+pos);
//  REP (i, pos) eprintf("%d %d\n", name[i].first, name[i].second);
//  REP (i, size) assert(U.same(nama[i*2].second, nama[i*2+1].second));

    REP (i, pos) dp[pow2(i/2)][i] = 0;
    REP (s, pow2(size)) REP (i, pos) if (s & pow2(i/2) && dp[s][i] < INF) {
        REP (j, pos) if (~s & pow2(j/2)) {
        assert(i != j);
        assert(name[i].second != name[j].second);
        double cst = dist(name[i].second, name[j].second);
        int ns = s | pow2(j/2);
        if (dp[ns][j^1] > dp[s][i] + cst) {
            dp[ns][j^1] = dp[s][i] + cst;
            pre[ns][j^1] = s * DP_MAX * 2 + i;
        }
        }
    }

    int SUP = pow2(size)-1;
    int cur = 0;
    REP (i, pos) if (dp[SUP][cur] > dp[SUP][i]) cur = i;

    REP (_, size-1) {
        int s = pre[SUP][cur] / (DP_MAX * 2);
        int i = pre[SUP][cur] % (DP_MAX * 2);
        int a = name[i].second;
        int b = name[cur^1].second;
        assert(deg[a] <= 1);
        assert(deg[b] <= 1);
        G[a].push_back(b);
        G[b].push_back(a); 
        deg[a]++; deg[b]++;
        SUP = s;
        cur = i;
    }
    }

    setOrdFromGraph();
    refineOrd();
}
void buildPath() {
    ord.clear();
    if (stop == 0) return;
    if (stop == 1) {
    ord.push_back(0);
    return;
    }

    REP (i, stop) G[i].clear();
    int cnt = 0;
    edges.resize(stop * (stop - 1) / 2);
    REP (j, stop) REP (i, j) {
    edges[cnt++] = make_pair(dist(i, j), i * stop + j);
    }
    memset(deg, 0, sizeof (int) * stop);
    UnionFind U(stop);
    sort(edges.begin(), edges.end());
    REP (i, cnt) {
    int a = edges[i].second / stop;
    int b = edges[i].second % stop;
    if (deg[a] < 2 && deg[b] < 2 && !U.same(a, b)) {
        G[a].push_back(b);
        G[b].push_back(a);
        deg[a]++; deg[b]++;
        U.link(a, b);
    }
    }

    setOrdFromGraph();
    refineOrd();
}

int pre[MAXNN][4][4];
bool end_points[MAXN][MAXN];

void addExtend() {
    memset(pre, -1, sizeof (int) * stop * 4 * 4);

    double (*dp)[4][4] = (double (*)[4][4])dp_buf;
    assert(sizeof dp == sizeof (void*));
    REP (i, stop) REP (a, 4) REP (b, 4) dp[i][a][b] = INF;

    int start = ord[0];
    REP (d0, 4) REP (t, 2) {
    int d1 = adj_d[d0][t];
    dp[0][d0][d1] = 0;
    pre[0][d0][d1] = -2;
    }

    int pre_r = R[start], pre_c = C[start];
    for (int i=1; i<stop; i++) {
    int id = ord[i];
    int cur_r = R[id], cur_c = C[id];
    REP (d0, 4) REP (t, 2) {
        int d1 = adj_d[d0][t];
        if (dp[i-1][d0][d1] == INF) continue;

        int pr = pre_r + dy[d1];
        int pc = pre_c + dx[d1];

        REP (d2, 4) REP (tt, 2) {
        int d3 = adj_d[d2][tt];
        int cr = cur_r + dy[d2];
        int cc = cur_c + dx[d2];

        if (pr == cr && pc == cc) continue;

        double cst = sqrt(sq(pr - cr) + sq(pc - cc));
        if (dp[i][d2][d3] > dp[i-1][d0][d1] + cst) {
            dp[i][d2][d3] = dp[i-1][d0][d1] + cst;
            pre[i][d2][d3] = d0 * 4 + d1;
        }
        }
    }
    pre_r = cur_r;  
    pre_c = cur_c;
    }

    {
    int d2 = 0, d3 = 2;
    REP (a, 4) REP (b, 4) if (dp[stop-1][a][b] < dp[stop-1][d2][d3]) {
        d2 = a;
        d3 = b;
    }

    static char buf[10011];
    for (int i=stop; i--;) {
        int id = ord[i];
        pre_r = R[id];
        pre_c = C[id];
        REP (t, 2) {
        int d = d3 ^ t;
        int pr = pre_r + dy[d];
        int pc = pre_c + dx[d];
        sprintf(buf, "%d %d", pr, pc);
        ret.push_back(buf);
        }
        REP (t, 2) {
        int d = d2 ^ t ^ 1;
        int pr = pre_r + dy[d];
        int pc = pre_c + dx[d];
        sprintf(buf, "%d %d", pr, pc);
        ret.push_back(buf);
        }


        int nd2 = pre[i][d2][d3] / 4;
        int nd3 = pre[i][d2][d3] % 4;
        d2 = nd2;
        d3 = nd3;
    }
    }
}

struct CrossStitch {
    vector<string> embroider(vector<string> F_) {
    F = move(F_);
        N = F.size();
    ret.clear();

        for (char color = 'a'; color <= 'z'; ++color) {
        findPosition(color);
        if (stop == 0) continue;

        if (N <= 40) {
        buildPathDp();
        } else {
        buildPath();
        }
        addExtend();
        }
        return ret;
    }
};

vector<string> readFileToVector(const string& filename)
{
    ifstream source;
    source.open(filename);
    vector<string> lines;
    string line;
    while (getline(source, line))
    {
        lines.push_back(line);
    }
    return lines;
}

void displayVector(const vector<string> v)
{
    for (int i(0); i != v.size(); ++i)
        cout << "\n" << v[i];
    cout << "\n the solution is: ";
}

int main(int argc, char* argv[]){

    //handling the input
    if(argc != 2){
        cerr << "error! Usage: "<< argv[0]
            << "input.txt" <<endl;
        return 1;
    }

    string f(argv[1]);
    vector<string> pattern = readFileToVector(f);
    
    //running the algorithm 
    vector<string> ret;
    CrossStitch crosstitch;
    ret =crosstitch.embroider(pattern);

    //visualize the result
    displayVector(ret);
    return 0;
}
