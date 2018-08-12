#include <assert.h>
#include <math.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <algorithm>
#include <map>
#include <queue>
#include <string>
#include <vector>

using namespace std;

//#define LOCAL
//#define VISUALIZER
//#define COMPUTE_STATS

#define NMAX 105
#define CMAX 22
#define MAXNN 100
#define PROB_COEF 4294967295U
#define TC_FREQ 2.5e9
#define LOCAL_FREQ 2.2e9

#if defined(LOCAL) || defined(VISUALIZER)
#define TIME_LIMIT 7.0//15.0
#else
#define TIME_LIMIT 9.88
#endif

inline double GetTime() {
    unsigned long long timelo, timehi;
    __asm__ volatile ("rdtsc" : "=a" (timelo), "=d" (timehi));
#if defined(LOCAL) || defined(VISUALIZER)
    return ((timehi << 32) + timelo) / LOCAL_FREQ;
#else
    return ((timehi << 32) + timelo) / TC_FREQ;
#endif
}

namespace SOLVE {
char A[NMAX][NMAX];
int N, C;
double dsqrt[2 * (NMAX + 1) * (NMAX + 1)];
int pozid[NMAX][NMAX], cid;
int pall[NMAX * NMAX][2];
int dall[NMAX * NMAX * 4][2];
int rtmp[CMAX][NMAX * NMAX], ctmp[CMAX][NMAX * NMAX], pidstart[CMAX], poz[CMAX][NMAX * NMAX], npoz[CMAX], nall;

#define myabs(x) (x + N)

double TEND;

void Init(const vector<string>& pattern) {
    TEND = GetTime() + TIME_LIMIT;
    N = pattern.size();
    C = nall = 0;
    memset(npoz, 0, sizeof(npoz));
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++) {
            A[i][j] = pattern[i][j];
            if (A[i][j] == '.') continue;
            cid = A[i][j] - 'a';
            if (cid + 1 > C) C = cid + 1;
            auto& npoz_cid = npoz[cid];
            rtmp[cid][npoz_cid] = i;
            ctmp[cid][npoz_cid++] = j;
        }
    for (cid = 0; cid < C; cid++) {
        pidstart[cid] = nall;
        const auto& npoz_cid = npoz[cid];
        const auto& rtmp_cid = rtmp[cid];
        const auto& ctmp_cid = ctmp[cid];
        auto& poz_cid = poz[cid];
        for (int k = 0; k < npoz_cid; k++) {
            const auto& i = rtmp_cid[k];
            const auto& j = ctmp_cid[k];
            pall[nall][0] = i;
            pall[nall][1] = j;
            dall[nall << 2][0] = i;
            dall[nall << 2][1] = j;
            dall[(nall << 2) | 1][0] = i + 1;
            dall[(nall << 2) | 1][1] = j + 1;
            dall[(nall << 2) | 2][0] = i;
            dall[(nall << 2) | 2][1] = j + 1;
            dall[(nall << 2) | 3][0] = i + 1;
            dall[(nall << 2) | 3][1] = j;
            pozid[i][j] = nall;
            poz_cid[k] = nall++;
        }
    }
    for (int i = 0; i <= N; i++) {
        for (int j = 0; j <= N; j++) {
            int d2 = i * i + j * j;
            dsqrt[d2] = sqrt(d2);
        }
    }
}

int vec[NMAX * NMAX][MAXNN + 1], nvec[NMAX * NMAX];
int vec2[NMAX * NMAX][MAXNN + 1], nvec2[NMAX * NMAX];
double dvec[NMAX * NMAX][MAXNN + 1];
double dvec2[NMAX * NMAX][MAXNN + 1];
double bscore[CMAX], total_bscore;
int bsol[CMAX][NMAX * NMAX * 2];
int nbsol[CMAX], ncsol;
int csol[NMAX * NMAX * 2];
char visited[NMAX * NMAX * 2];
int cpoz[NMAX * NMAX * 2], pp[2];

void OptimizeBestSolForSameCellDiagonals() {
    const auto& nbsol_cid = nbsol[cid];
    auto& bsol_cid = bsol[cid];
    const auto& npoz_cid = npoz[cid];
    const auto& poz_cid = poz[cid];

    for (int i = 0; i < nbsol_cid; i++) cpoz[bsol_cid[i] >> 1] = i;

    bool updated = true;
    while (updated) {
        updated = false;
        for (int i = 0; i < npoz_cid; i++) {
            int pid = poz_cid[i];
            int dpid0 = pid << 1;
            int dpid1 = dpid0 | 1;
            pp[0] = cpoz[dpid0]; pp[1] = cpoz[dpid1];
            double dmin = 1e30;
            int o0best = -1, o1best = -1, pporderbest = -1;
            dpid0 <<= 1; dpid1 <<= 1;
            for (int pporder = 0; pporder <= 1; pporder++)
                for (int o0 = 0; o0 <= 1; o0++)
                    for (int o1 = 0; o1 <= 1; o1++) {
                        double d = 0.0;
                        
                        int p0 = pp[pporder], p1 = pp[pporder ^ 1];

                        int r01 = dall[dpid0 | o0][0], c01 = dall[dpid0 | o0][1];
                        int r02 = dall[dpid0 | (o0 ^ 1)][0], c02 = dall[dpid0 | (o0 ^ 1)][1];

                        int r11 = dall[dpid1 | o1][0], c11 = dall[dpid1 | o1][1];
                        int r12 = dall[dpid1 | (o1 ^ 1)][0], c12 = dall[dpid1 | (o1 ^ 1)][1];

                        if (p0 > 0) {
                            int prevdpido = bsol_cid[p0 - 1] ^ 1;
                            const auto& dall_prevdpido = dall[prevdpido];
                            int dx = r01 - dall_prevdpido[0], dy = c01 - dall_prevdpido[1];
                            if (dx == 0 && dy == 0) continue;
                            else d += dsqrt[dx * dx + dy * dy];
                        }

                        if (p0 + 1 < nbsol_cid) {
                            int nextdpido = bsol_cid[p0 + 1];
                            const auto& dall_nextdpido = dall[nextdpido];
                            int dx = r02 - dall_nextdpido[0], dy = c02 - dall_nextdpido[1];
                            if (dx == 0 && dy == 0) continue;
                            else d += dsqrt[dx * dx + dy * dy];
                        }

                        if (p1 > 0) {
                            int prevdpido = bsol_cid[p1 - 1] ^ 1;
                            const auto& dall_prevdpido = dall[prevdpido];
                            int dx = r11 - dall_prevdpido[0], dy = c11 - dall_prevdpido[1];
                            if (dx == 0 && dy == 0) continue;
                            else d += dsqrt[dx * dx + dy * dy];
                        }

                        if (p1 + 1 < nbsol_cid) {
                            int nextdpido = bsol_cid[p1 + 1];
                            const auto& dall_nextdpido = dall[nextdpido];
                            int dx = r12 - dall_nextdpido[0], dy = c12 - dall_nextdpido[1];
                            if (dx == 0 && dy == 0) continue;
                            else d += dsqrt[dx * dx + dy * dy];
                        }
                    
                        if (d < dmin - 1e-7) {
                            dmin = d;
                            o0best = o0;
                            o1best = o1;
                            pporderbest = pporder;
                        }
                    }
            if (pporderbest == 1 || o0best != (bsol_cid[pp[0]] & 1) || o1best != (bsol_cid[pp[1]] & 1)) {
                if (pporderbest == 1) {
                    bsol_cid[pp[0]] = dpid1 | o1best;
                    bsol_cid[pp[1]] = dpid0 | o0best;
                    cpoz[dpid0 >> 1] = pp[1];
                    cpoz[dpid1 >> 1] = pp[0];
                } else {
                    bsol_cid[pp[0]] = dpid0 | o0best;
                    bsol_cid[pp[1]] = dpid1 | o1best;
                }
                updated = true;
            }
        }
    }
    auto& bscore_cid = bscore[cid];
    bscore_cid = 0.0;
    for (int i = 1; i < nbsol_cid; i++) {
        int dpidio = bsol_cid[i];
        const auto& dall_dpidio = dall[dpidio];
        int prevdpido = bsol_cid[i - 1] ^ 1;
        const auto& dall_prevdpido = dall[prevdpido];
        int dx = dall_dpidio[0] - dall_prevdpido[0], dy = dall_dpidio[1] - dall_prevdpido[1];
        bscore_cid += dsqrt[dx * dx + dy * dy];
    }
}

vector<pair<int, double>> mstvec[NMAX * NMAX];
int pidcand[NMAX * NMAX], npidcand, pidparent[NMAX * NMAX], pidsel[NMAX * NMAX], npidsel;
double dtocand[NMAX * NMAX];
int mainpath[NMAX * NMAX], nmainpath, pidu, pidv;
char pidvisited[NMAX * NMAX];

bool MSTDFS(int pid) {
    pidvisited[pid] = 1;
    mainpath[nmainpath++] = pid;
    if (pid == pidv) return true;
    for (const auto& pidvec_pair : mstvec[pid]) {
        const auto& pidvec = pidvec_pair.first;
        if (pidvisited[pidvec]) continue;
        if (MSTDFS(pidvec)) return true;
    }
    nmainpath--;
    return false;
}

void MSTDFS2(int pid) {
    pidvisited[pid] = 1;
    auto& bsol_cid = bsol[cid];
    auto& nbsol_cid = nbsol[cid];
    if (nbsol_cid > 0) {
        double dmin = 1e30;
        int dbest = -1, obest = -1;
        for (int d = 0; d <= 1; d++)
            for (int o = 0; o <= 1; o++) {
                const auto& dall_pid_d_o = dall[(pid << 2) | (d << 1) | o];
                int prevdpido = bsol_cid[nbsol_cid - 1] ^ 1;
                const auto& dall_prevdpido = dall[prevdpido];
                int dx = dall_pid_d_o[0] - dall_prevdpido[0], dy = dall_pid_d_o[1] - dall_prevdpido[1];
                if (dx == 0 && dy == 0) continue;
                double dd = dsqrt[dx * dx + dy * dy];
                if (dd < dmin) {
                    dmin = dd;
                    dbest = d;
                    obest = o;
                }
        }
        bsol_cid[nbsol_cid++] = (pid << 2) | (dbest << 1) | obest;
    } else {
        bsol_cid[nbsol_cid++] = pid << 2;
    }
    int d2 = ((bsol_cid[nbsol_cid - 1] >> 1) & 1) ^ 1;
    for (const auto& pidvec_pair : mstvec[pid]) {
        const auto& pidvec = pidvec_pair.first;
        if (!pidvisited[pidvec]) MSTDFS2(pidvec);
    }

    double dmin = 1e30;
    int obest = -1;
    for (int o = 0; o <= 1; o++) {
        const auto& dall_pid_d2_o = dall[(pid << 2) | (d2 << 1) | o];
        int prevdpido = bsol_cid[nbsol_cid - 1] ^ 1;
        const auto& dall_prevdpido = dall[prevdpido];
        int dx = dall_pid_d2_o[0] - dall_prevdpido[0], dy = dall_pid_d2_o[1] - dall_prevdpido[1];
        if (dx == 0 && dy == 0) continue;
        double dd = dsqrt[dx * dx + dy * dy];
        if (dd < dmin) {
            dmin = dd;
            obest = o;
        }
    }
    //assert(obest >= 0);
    bsol_cid[nbsol_cid++] = (pid << 2) | (d2 << 1) | obest;
}

double distmax, dcurr;

void MSTDFS3(int pid) {
    pidvisited[pid] = 1;
    if (dcurr > distmax) {
        distmax = dcurr;
        pidu = pid;
    }
    for (const auto& pidvec_pair : mstvec[pid]) {
        const auto& pidvec = pidvec_pair.first;
        if (pidvisited[pidvec]) continue;
        int dx = pall[pid][0] - pall[pidvec][0], dy = pall[pid][1] - pall[pidvec][1];
        const auto& d = dsqrt[dx * dx + dy * dy];
        dcurr += d;
        MSTDFS3(pidvec);
        dcurr -= d;
    }
}

int NNMAX, ROOT;
double EMAX;

void MSTDFSForNN(int x) {
    pidvisited[x] = 1;
    const auto& pall_root = pall[ROOT];
    for (const auto& pidvec_pair : mstvec[x]) {
        const auto& y = pidvec_pair.first;
        if (pidvisited[y]) continue;
        const auto& d = pidvec_pair.second;
        double OLD_EMAX = EMAX;
        if (d > EMAX) EMAX = d;
        const auto& pall_y = pall[y];
        int dx = pall_root[0] - pall_y[0], dy = pall_root[1] - pall_y[1];
        double cy = dsqrt[dx * dx + dy * dy];
        cy -= EMAX;
        auto& nvec_ROOT = nvec[ROOT];
        auto& vec_ROOT = vec[ROOT];
        auto& dvec_ROOT = dvec[ROOT];
        if (nvec_ROOT < NNMAX) {
            vec_ROOT[nvec_ROOT] = y;
            dvec_ROOT[nvec_ROOT++] = cy;
        } else {
            int pmax = 0;
            for (int i = 1; i < nvec_ROOT; i++)
                if (dvec_ROOT[i] > dvec_ROOT[pmax])
                    pmax = i;
            if (cy < dvec_ROOT[pmax]) {
                vec_ROOT[pmax] = y;
                dvec_ROOT[pmax] = cy;
            }
            /*if (cy < dvec_ROOT[pmax] + 1e-3) {
                if (cy < dvec_ROOT[pmax] - 1e-3) {
                    vec_ROOT[pmax] = y;
                    dvec_ROOT[pmax] = cy;
                } else {
                    vec_ROOT[nvec_ROOT] = y;
                    dvec_ROOT[nvec_ROOT++] = cy;
                }
            }*/
        }
        MSTDFSForNN(y);
        EMAX = OLD_EMAX;
    }
}

void MSTSol() {
    const auto& poz_cid = poz[cid];
    const auto& npoz_cid = npoz[cid];

    npidcand = 0;
    for (int i = 0; i < npoz_cid; i++) {
        int pid = poz_cid[i];
        mstvec[pid].clear();
        pidcand[npidcand++] = pid;
    }

    int psel = pidsel[0] = pidcand[--npidcand];
    npidsel = 1;
    for (int i = 0; i < npidcand; i++) {
        int pcand = pidcand[i];
        int dx = pall[pcand][0] - pall[psel][0], dy = pall[pcand][1] - pall[psel][1];
        dtocand[pcand] = dsqrt[dx * dx + dy * dy];
        pidparent[pcand] = psel;
    }
    
    double mstlen = 0.0;

    while (npidcand > 0) {
        double dmin = 1e30;
        int pcand_poz_best = -1;
        for (int i = 0; i < npidcand; i++) {
            int pcand = pidcand[i];
            if (dtocand[pcand] < dmin) {
                dmin = dtocand[pcand];
                pcand_poz_best = i;
            }
        }
        mstlen += dmin;
        psel = pidcand[pcand_poz_best];
        pidcand[pcand_poz_best] = pidcand[--npidcand];
        pidsel[npidsel++] = psel;
        mstvec[psel].push_back({pidparent[psel], dmin});
        mstvec[pidparent[psel]].push_back({psel, dmin});
        for (int i = 0; i < npidcand; i++) {
            int pcand = pidcand[i];
            int dx = pall[pcand][0] - pall[psel][0], dy = pall[pcand][1] - pall[psel][1];
            const auto& d = dsqrt[dx * dx + dy * dy];
            if (d < dtocand[pcand]) {
                dtocand[pcand] = d;
                pidparent[pcand] = psel;
            }
        }       
    }
    for (int i = 0; i < npoz_cid; i++) {
        ROOT = poz_cid[i];
        nvec[ROOT] = nvec2[ROOT] = 0;
        EMAX = 0.0;
        for (int j = 0; j < npoz_cid; j++) pidvisited[poz_cid[j]] = 0;
        MSTDFSForNN(ROOT);
        vec[ROOT][nvec[ROOT]++] = ROOT;
        //vec2[ROOT][nvec2[ROOT]++] = ROOT;
    }

    pidu = -1;
    dcurr = 0.0;
    distmax = -1.0;
    for (int i = 0; i < npoz_cid; i++) {
        int pid = poz_cid[i];
        pidvisited[pid] = 0;
    }
    MSTDFS3(poz_cid[0]);
    pidv = pidu;
    dcurr = 0.0;
    distmax = -1.0;
    for (int i = 0; i < npoz_cid; i++) {
        int pid = poz_cid[i];
        pidvisited[pid] = 0;
    }
    MSTDFS3(pidv);
    
    for (int i = 0; i < npoz_cid; i++) {
        int pid = poz_cid[i];
        pidvisited[pid] = 0;
    }
    nmainpath = 0;
    MSTDFS(pidu);

    for (int i = 0; i < npoz_cid; i++) {
        int pid = poz_cid[i];
        pidvisited[pid] = 0;
    }

    for (int i = 0; i < nmainpath; i++) {
        int pid = mainpath[i];
        if (i > 0) pidvisited[mainpath[i - 1]] = 1;
        if (i + 1 < nmainpath) pidvisited[mainpath[i + 1]] = 1;
        MSTDFS2(pid);
    }

    // Fix the orientations.
    const auto& nbsol_cid = nbsol[cid];
    auto& bsol_cid = bsol[cid];
    
    for (int i = 1; i < nbsol_cid; i++) {
        int dpidio = bsol_cid[i];
        const auto& dall_dpidio = dall[dpidio];
        int ri1 = dall_dpidio[0], ci1 = dall_dpidio[1];
        int prevdpido = bsol_cid[i - 1] ^ 1;
        const auto& dall_prevdpido = dall[prevdpido];
        int rprev = dall_prevdpido[0], cprev = dall_prevdpido[1];
        if (rprev == ri1 && cprev == ci1) bsol_cid[i] ^= 1;
    }

    OptimizeBestSolForSameCellDiagonals();
}

#define MAXELEMS 9

double dmin[1 << (2 * MAXELEMS)][2 * MAXELEMS][2];
unsigned char pj[1 << (2 * MAXELEMS)][2 * MAXELEMS][2];
int sin[2 * MAXELEMS], nsin;

void FindInitialSolution() {
    //fprintf(stderr, "avg=%.3lf\n", (double) nall / C);
    static const int MIN_AVG_NPOZ_FOR_SMALL_NNMAX = 50;
    static const int MIN_AVG_NPOZ1_FOR_VERY_SMALL_NNMAX = 223;
    static const int MIN_AVG_NPOZ2_FOR_VERY_SMALL_NNMAX = 600;
    if (C <= 5 || nall < MIN_AVG_NPOZ_FOR_SMALL_NNMAX * C) NNMAX = 8;
    else {
        NNMAX = 4;
        if (nall >= MIN_AVG_NPOZ2_FOR_VERY_SMALL_NNMAX * C ||
            (nall >= MIN_AVG_NPOZ1_FOR_VERY_SMALL_NNMAX * C && C >= 8))
            NNMAX = 3;
    }
    total_bscore = 0.0;
    for (cid = 0; cid < C; cid++) {
        nbsol[cid] = 0;
        bscore[cid] = 0.0;
        if (npoz[cid] <= MAXELEMS) {
            const auto& npoz_cid = npoz[cid];
            const auto& poz_cid = poz[cid];
            ncsol = 0;
            for (int i = 0; i < npoz[cid]; i++) {
                int pid = poz_cid[i];
                csol[ncsol++] = pid << 1;
                csol[ncsol++] = (pid << 1) | 1;
            }
            int nsets = 1 << ncsol;
            for (int s = 1; s < nsets; s++) {
                nsin = 0;
                for (int i = 0; i < ncsol; i++)
                    if (s & (1 << i)) sin[nsin++] = i;
                auto& dmin_s = dmin[s];
                auto& pj_s = pj[s];
                if (nsin == 1) {
                    dmin_s[sin[0]][0] = dmin_s[sin[0]][1] = 0.0;
                    continue;
                }
                for (int k = 0; k < nsin; k++) {
                    int i = sin[k];
                    int dpidi = csol[i] << 1;
                    dmin_s[i][0] = dmin_s[i][1] = 1e30;
                    int si = s ^ (1 << i);
                    const auto& dmin_si = dmin[si];
                    for (int ki = 0; ki < nsin; ki++) {
                        if (k == ki) continue;
                        int j = sin[ki];
                        int dpidj = csol[j] << 1;
                        for (int oi = 0; oi <= 1; oi++) {
                            const auto& dall_dpidio = dall[dpidi | oi];
                            int ri = dall_dpidio[0];
                            int ci = dall_dpidio[1];
                            for (int oj = 0; oj <= 1; oj++) {
                                const auto& dall_dpidjo = dall[dpidj | (oj ^ 1)];
                                int dx = ri - dall_dpidjo[0], dy = ci - dall_dpidjo[1];
                                if (dx == 0 && dy == 0) continue;
                                const double d = dmin_si[j][oj] + dsqrt[dx * dx + dy * dy];
                                if (d < dmin_s[i][oi]) {
                                    dmin_s[i][oi] = d;
                                    pj_s[i][oi] = (j << 1) | oj;
                                }
                            }
                        }
                    }
                }
            }
            auto& bscore_cid = bscore[cid];
            bscore_cid = 1e30;
            int ibest = -1, obest = -1;
            const auto& dmin_nsets_m1 = dmin[nsets - 1];
            for (int i = 0; i < ncsol; i++)
                for (int oi = 0; oi <= 1; oi++)
                    if (dmin_nsets_m1[i][oi] < bscore_cid) {
                        bscore_cid = dmin_nsets_m1[i][oi];
                        ibest = i;
                        obest = oi;
            }
            auto& nbsol_cid = nbsol[cid];
            auto& bsol_cid = bsol[cid];
            nbsol_cid = 0;
            int s = nsets - 1;
            while (s > 0) {
                bsol_cid[nbsol_cid++] = (csol[ibest] << 1) | obest;
                int j = pj[s][ibest][obest];
                s ^= (1 << ibest);
                ibest = j >> 1;
                obest = j & 1;
            }
            reverse(&bsol_cid[0], &bsol_cid[nbsol_cid]);
        } else {
            MSTSol();
        }
        total_bscore += bscore[cid];
    }
}

namespace XOR128 {
unsigned int xx, yy, zz, uu;

void reset(unsigned int seed) {
    xx = seed;
    yy = 362436069;
    zz = 521288629;
    uu = 786232308;
}

inline unsigned int rand() {
    unsigned int t = (xx ^ (xx << 11));
    xx = yy; yy = zz; zz = uu;
    return (uu = (uu ^ (uu >> 19)) ^ (t ^ (t >> 8)));
}
}

unsigned int fast_rand_seed;
#define fast_rand (fast_rand_seed = (214013U * fast_rand_seed + 2531011U))

inline double fast_exp(double y) {
    double d;
   *((int*)(&d) + 0) = 0;
   *((int*)(&d) + 1) = (int)(1512775 * y + 1072632447);
   return d;
}

double coef;
#define Accept(dif) (fast_exp(-(dif) * coef) * PROB_COEF >= fast_rand)

int wdpid[2 * NMAX * NMAX];
double w[NMAX * NMAX * 2];
int pivot_index, pivot_cntsel, store_index, vtmp, ppivot;
double pivot_value;

const double WTHRESHOLD = 2.01;

int QuickSelect(int left, int right) {
    if (left == right) return left;
    if (left > right) {
        if (right >= 0) return right;
        return left;
    }
    pivot_index = left + (fast_rand % (right - left + 1));
    pivot_value = w[wdpid[pivot_index]];
    vtmp = wdpid[right]; wdpid[right] = wdpid[pivot_index]; wdpid[pivot_index] = vtmp;

    store_index = left;
    for (int i = left; i < right; i++) {
        int dpid = wdpid[i];
        if (w[dpid] > pivot_value) {
            vtmp = wdpid[store_index]; wdpid[store_index] = dpid; wdpid[i] = vtmp;
            store_index++;
        }
    }

    vtmp = wdpid[right]; wdpid[right] = wdpid[store_index]; wdpid[store_index] = vtmp;
    
    if (w[wdpid[store_index]] < WTHRESHOLD)
        return QuickSelect(left, store_index - 1);
    return QuickSelect(store_index + 1, right);
}

double cscore, init_bscore[CMAX];
int NSEL;
unsigned int num_modified_elems;

#define KMAX 10

unsigned int selected[NMAX * NMAX * 2], selected_idx;
int pozsel[KMAX], dpo[KMAX][2], best_order[KMAX][2];
int tmpcsol[NMAX * NMAX * 2];
int m[NMAX * NMAX * 2];
int pselmin[KMAX], partsidx[KMAX][2];
double init_bscore_cid, threshold;
int nattemptskswap, nacceptkswap, nimprovekswap;

inline bool TryKSwapSolveOptimally2(int K) {
#ifdef COMPUTE_STATS
    nattemptskswap++;
#endif
    selected_idx++;
    int wpoz, dpidu, pidu, dpidv, pidv, poz, nelems = 0;
    for (int i = 0; i < K; i++) {
        int ntries = 0;
        do {
            ntries++;
            dpidu = wdpid[XOR128::rand() % NSEL];
            poz = cpoz[dpidu];
        } while (selected[poz] == selected_idx & ntries < 10);
        if (ntries == 10) break;
        dpidu = csol[poz];
        selected[poz] = selected_idx;
        pozsel[nelems++] = poz;
        pidu = dpidu >> 2;
        const auto& vec_pidu = vec[pidu];
        const auto& nvec_pidu = nvec[pidu];
        const auto& dall_dpidux = dall[dpidu ^ 1];
        int ru = dall_dpidux[0], cu = dall_dpidux[1], rv  = -1, cv = -1;
        dpidu >>= 1;
        ntries = 0;
        do {
            ntries++;
            pidv = vec_pidu[XOR128::rand() % nvec_pidu];
            if (pidu != pidv) dpidv = (pidv << 1) | (fast_rand & 1);
            else dpidv = dpidu ^ 1;
            poz = cpoz[dpidv];
            dpidv = csol[poz];
            const auto& dall_dpidvx = dall[dpidv ^ 1];
            rv = dall_dpidvx[0], cv = dall_dpidvx[1];
        } while ((selected[poz] == selected_idx || (rv == ru && cv == cu)) && ntries < 10);
        if (ntries == 10) {
            nelems--;
            break;
        }
        selected[poz] = selected_idx;
        pozsel[nelems++] = poz;
        m[pozsel[nelems - 1]] = pozsel[nelems - 2];
        m[pozsel[nelems - 2]] = pozsel[nelems - 1];
    }

    K = nelems;
    sort(&pozsel[0], &pozsel[K]);

    pselmin[0] = 0;
    for (int i = 1; i <= K; i++) pselmin[i] = pozsel[i - 1] + 1;
    pozsel[K] = ncsol - 1;

    double oldscore = 0.0;
    int imax = pozsel[K - 1] < ncsol - 1 ? K : K - 1;
    for (int i = 0; i < imax; i++) {
        if (pozsel[i] == ncsol - 1) break;
        int dpidio = csol[pozsel[i] + 1];
        const auto& dall_dpidio_init = dall[dpidio];
        int prevdpido = csol[pozsel[i]] ^ 1;
        const auto& dall_prevdpido_init = dall[prevdpido];
        int dx = dall_dpidio_init[0] - dall_prevdpido_init[0], dy = dall_dpidio_init[1] - dall_prevdpido_init[1];
        oldscore += dsqrt[dx * dx + dy * dy];
    }

    int pidx = 0;
    double base_score = 0.0;
    for (int i = 0; i < K; i++) {
        int mpart = -1, mm = m[pozsel[i]];
        for (int j = i + 1; j < K; j++)
            if (mm == pozsel[j]) {
                mpart = j;
                break;
            }
        if (mpart < 0) continue;
        
        int dpidio = csol[pozsel[i]] ^ 1;
        const auto& dall_dpidio_init = dall[dpidio];
        int prevdpido = csol[pozsel[mpart]] ^ 1;
        const auto& dall_prevdpido_init = dall[prevdpido];
        int dx = dall_dpidio_init[0] - dall_prevdpido_init[0], dy = dall_dpidio_init[1] - dall_prevdpido_init[1];
        base_score += dsqrt[dx * dx + dy * dy];
        if (base_score >= oldscore) return false;       
        partsidx[pidx][0] = i;
        partsidx[pidx][1] = mpart;
        pidx++;
    }

    if (base_score >= 0.666 * oldscore - 1e-7) return false;

    if (pozsel[K - 1] + 1 < ncsol) {
        partsidx[pidx][0] = partsidx[pidx][1] = K;
        pidx++;
    }

    K = pidx;

    for (int i = 0; i < K; i++) {
        dpo[i][0] = csol[pselmin[partsidx[i][0]]];
        if (partsidx[i][0] != partsidx[i][1])
            dpo[i][1] = csol[pselmin[partsidx[i][1]]];
        else
            dpo[i][1] = csol[pozsel[partsidx[i][0]]] ^ 1;
    }

    int nsets = 1 << K;
    for (int s = 1; s < nsets; s++) {
        nsin = 0;
        for (int i = 0; i < K; i++)
            if (s & (1 << i)) sin[nsin++] = i;
        auto& dmin_s = dmin[s];
        auto& pj_s = pj[s];
        if (nsin == 1) {
            dmin_s[sin[0]][0] = dmin_s[sin[0]][1] = 0.0;
            continue;
        }
        for (int k = 0; k < nsin; k++) {
            int i = sin[k];
            const auto& dpo_i = dpo[i];
            dmin_s[i][0] = dmin_s[i][1] = 1e30;
            int si = s ^ (1 << i);
            const auto& dmin_si = dmin[si];
            for (int ki = 0; ki < nsin; ki++) {
                if (k == ki) continue;
                int j = sin[ki];
                for (int oi = 0; oi <= 1; oi++) {
                    const auto& dall_dpidio = dall[dpo_i[oi]];
                    int ri = dall_dpidio[0];
                    int ci = dall_dpidio[1];
                    const auto& dpo_j = dpo[j];
                    for (int oj = 0; oj <= 1; oj++) {
                        const auto& dall_dpidjo = dall[dpo_j[oj ^ 1]];
                        int dx = ri - dall_dpidjo[0], dy = ci - dall_dpidjo[1];
                        if (dx == 0 && dy == 0) continue;
                        const double d = dmin_si[j][oj] + dsqrt[dx * dx + dy * dy];
                        if (d < dmin_s[i][oi]) {
                            dmin_s[i][oi] = d;
                            pj_s[i][oi] = (j << 1) | oj;
                        }
                    }
                }
            }
        }
    }
    double tmp_bscore = 1e30;
    int ibest = -1, obest = -1;
    const auto& dmin_nsets_m1 = dmin[nsets - 1];
    for (int i = 0; i < K; i++)
        for (int oi = 0; oi <= 1; oi++)
            if (dmin_nsets_m1[i][oi] < tmp_bscore) {
                tmp_bscore = dmin_nsets_m1[i][oi];
                ibest = i;
                obest = oi;
            }

    tmp_bscore += base_score;
    double dif = tmp_bscore - oldscore;

    if (dif < -1e-7 || (cscore + dif <= threshold * init_bscore_cid && Accept(dif))) {
#ifdef COMPUTE_STATS
        nacceptkswap++;
#endif
        int idx = 0;
        int s = nsets - 1;
        while (s > 0) {
            best_order[idx][0] = ibest;
            best_order[idx][1] = obest;
            idx++;
            int j = pj[s][ibest][obest];
            s ^= (1 << ibest);
            ibest = j >> 1;
            obest = j & 1;
        }
        reverse(&best_order[0], &best_order[idx]);

        cscore += dif;
        int tmpncsol = 0;
        for (int i = 0; i < K; i++) {
            const auto& best_order_i = best_order[i];
            pidx = best_order_i[0];
            if (best_order_i[1] == 0) {
                int pozmin = pselmin[partsidx[pidx][0]], pozmax = pozsel[partsidx[pidx][0]];
                for (int j = pozmin; j <= pozmax; j++)
                    tmpcsol[tmpncsol++] = csol[j];
                if (partsidx[pidx][0] != partsidx[pidx][1]) {
                    pozmin = pselmin[partsidx[pidx][1]];
                    pozmax = pozsel[partsidx[pidx][1]];
                    for (int j = pozmax; j >= pozmin; j--)
                        tmpcsol[tmpncsol++] = csol[j] ^ 1;
                }
            } else {
                if (partsidx[pidx][0] == partsidx[pidx][1]) {
                    int pozmin = pselmin[partsidx[pidx][1]], pozmax = pozsel[partsidx[pidx][1]];
                    for (int j = pozmax; j >= pozmin; j--)
                        tmpcsol[tmpncsol++] = csol[j] ^ 1;
                } else {
                    int pozmin = pselmin[partsidx[pidx][1]], pozmax = pozsel[partsidx[pidx][1]];
                    for (int j = pozmin; j <= pozmax; j++)
                        tmpcsol[tmpncsol++] = csol[j];
                    if (partsidx[pidx][0] != partsidx[pidx][1]) {
                        pozmin = pselmin[partsidx[pidx][0]];
                        pozmax = pozsel[partsidx[pidx][0]];
                        for (int j = pozmax; j >= pozmin; j--)
                            tmpcsol[tmpncsol++] = csol[j] ^ 1;
                    }
                }
            }
        }       
        memcpy(&csol[0], &tmpcsol[0], ncsol * sizeof(int));
        for (int i = 0; i < ncsol; i++) cpoz[csol[i] >> 1] = i;
    
        auto &bscore_cid = bscore[cid];
        if (cscore < bscore_cid - 1e-7) {
#ifdef COMPUTE_STATS
            nimprovekswap++;
#endif
            bscore_cid = cscore;
            memcpy(&bsol[cid][0], &csol[0], ncsol * sizeof(int));
        }
        
        num_modified_elems += ncsol;
    }
    return true;
}

#define TMAX 1000001
double sacoef[TMAX];

int nattemptso2, nimproveo2;

inline void SwapAndReorientTwoDiagonals() {
    // Try to change the orientations / swap the diagonals of the same cell.
#ifdef COMPUTE_STATS
    nattemptso2++;
#endif
    int wpozu, pozu, pidu, dpidu;
    if (fast_rand & 1) {
        pozu = XOR128::rand() % ncsol;
        pidu = csol[pozu] >> 2;
    } else {
        wpozu = XOR128::rand() % NSEL;          
        dpidu = wdpid[wpozu];
        pidu = dpidu >> 1;
        pozu = cpoz[dpidu];
    }
    int dpid0 = pidu << 1;

    int dpid1 = (pidu << 1) | 1;
        
    pp[0] = cpoz[dpid0]; pp[1] = cpoz[dpid1];
    if (pp[0] > pp[1]) {
        int tmp = pp[0]; pp[0] = pp[1]; pp[1] = tmp;
        tmp = dpid0; dpid0 = dpid1; dpid1 = tmp;
    }
    int o0init = csol[pp[0]] & 1, o1init = csol[pp[1]] & 1;
    double dmin = 1e30, dbase = 1e30;
    int o0best = -1, o1best = -1, pporderbest = -1;
    dpid0 <<= 1; dpid1 <<= 1;
    for (int pporder = 0; pporder <= 1; pporder++)
        for (int o0 = 0; o0 <= 1; o0++)
            for (int o1 = 0; o1 <= 1; o1++) {
                if (pporder == 1) {
                    csol[pp[0]] = dpid1 | o1;
                    csol[pp[1]] = dpid0 | o0;
                } else {
                    csol[pp[0]] = dpid0 | o0;
                    csol[pp[1]] = dpid1 | o1;
                }

                double d = 0.0;
                int p0 = pp[pporder], p1 = pp[pporder ^ 1];
                const auto& dall_pidu_o0 = dall[dpid0 | o0];
                int r01 = dall_pidu_o0[0], c01 = dall_pidu_o0[1];
                const auto& dall_pidu_o0x = dall[dpid0 | (o0 ^ 1)];
                int r02 = dall_pidu_o0x[0], c02 = dall_pidu_o0x[1];
                const auto& dall_pidux_o1 = dall[dpid1 | o1];
                int r11 = dall_pidux_o1[0], c11 = dall_pidux_o1[1];
                const auto& dall_pidux_o1x = dall[dpid1 | (o1 ^ 1)];
                int r12 = dall_pidux_o1x[0], c12 = dall_pidux_o1x[1];
                int p0p1 = p0 + 1, p1p1 = p1 + 1;

                if (p0 > 0) {
                    int prevdpido = csol[p0 - 1] ^ 1;
                    const auto& dall_prevdpido = dall[prevdpido];
                    int dx = r01 - dall_prevdpido[0], dy = c01 - dall_prevdpido[1];
                    if (dx == 0 && dy == 0) continue;
                    else d += dsqrt[dx * dx + dy * dy];
                }
    
                if (p0p1 < ncsol && p0p1 != p1) {
                    int nextdpido = csol[p0p1];
                    const auto& dall_nextdpido = dall[nextdpido];
                    int dx = r02 - dall_nextdpido[0], dy = c02 - dall_nextdpido[1];
                    if (dx == 0 && dy == 0) continue;
                    else d += dsqrt[dx * dx + dy * dy];
                }

                if (p1 > 0) {
                    int prevdpido = csol[p1 - 1] ^ 1;
                    const auto& dall_prevdpido = dall[prevdpido];
                    int dx = r11 - dall_prevdpido[0], dy = c11 - dall_prevdpido[1];
                    if (dx == 0 && dy == 0) continue;
                    else d += dsqrt[dx * dx + dy * dy];
                }

                if (p1p1 < ncsol && p1p1 != p0) {
                    int nextdpido = csol[p1 + 1];
                    const auto& dall_nextdpido = dall[nextdpido];
                    int dx = r12 - dall_nextdpido[0], dy = c12 - dall_nextdpido[1];
                    if (dx == 0 && dy == 0) continue;
                    else d += dsqrt[dx * dx + dy * dy];
                }
    
                if (pporder == 0 && o0 == o0init && o1 == o1init) dbase = d;
                if (d < dmin - 1e-7) {
                    dmin = d;
                    o0best = o0;
                    o1best = o1;
                    pporderbest = pporder;
                }
            }
    double dif = dmin - dbase;
    if (pporderbest == 1) {
        csol[pp[0]] = dpid1 | o1best;
        csol[pp[1]] = dpid0 | o0best;
        cpoz[dpid0 >> 1] = pp[1];
        cpoz[dpid1 >> 1] = pp[0];
    } else {
        csol[pp[0]] = dpid0 | o0best;
        csol[pp[1]] = dpid1 | o1best;
    }
    cscore += dif;
    auto& bscore_cid = bscore[cid];
    if (cscore < bscore_cid - 1e-7) {
#ifdef COMPUTE_STATS
        nimproveo2++;
#endif
        bscore_cid = cscore;
        memcpy(&bsol[cid][0], &csol[0], ncsol * sizeof(int));
    }
}

int nattemptso1, naccepto1, nimproveo1;

inline void ReorientOneDiagonal() {
    // Try to change orientation of a diagonal.
#ifdef COMPUTE_STATS
    nattemptso1++;
#endif
    int wpozu, dpidu, pozu;
    if (fast_rand & 1) {
        wpozu = XOR128::rand() % NSEL;          
        dpidu = wdpid[wpozu];
        pozu = cpoz[dpidu];
    } else {
        pozu = XOR128::rand() % ncsol;
    }
        
    int dpiduo = csol[pozu];
    const auto& dall_dpiduo = dall[dpiduo];
    const auto& dall_dpiduox = dall[dpiduo ^ 1];
    double dif = 0.0;
    if (pozu > 0) {
        int dpidu_prevo = csol[pozu - 1] ^ 1;
        const auto& dall_dpidu_prevo = dall[dpidu_prevo];
        int dx = dall_dpiduox[0] - dall_dpidu_prevo[0], dy = dall_dpiduox[1] - dall_dpidu_prevo[1];
        if (dx == 0 && dy == 0) return;
        dif += dsqrt[dx * dx + dy * dy];
        dx = dall_dpiduo[0] - dall_dpidu_prevo[0];
        dy = dall_dpiduo[1] - dall_dpidu_prevo[1];
        dif -= dsqrt[dx * dx + dy * dy];
    }
    if (pozu + 1 < ncsol) {
        int dpidu_nexto = csol[pozu + 1];
        const auto& dall_dpidu_nexto = dall[dpidu_nexto];
        int dx = dall_dpiduo[0] - dall_dpidu_nexto[0], dy = dall_dpiduo[1] - dall_dpidu_nexto[1];
        if (dx == 0 && dy == 0) return;
        dif += dsqrt[dx * dx + dy * dy];
        dx = dall_dpiduox[0] - dall_dpidu_nexto[0];
        dy = dall_dpiduox[1] - dall_dpidu_nexto[1];
        dif -= dsqrt[dx * dx + dy * dy];
    }
    if (dif < -1e-7) {
#ifdef COMPUTE_STATS
        naccepto1++;
#endif
        cscore += dif;
        csol[pozu] ^= 1;
        auto& bscore_cid = bscore[cid];
        if (cscore < bscore_cid - 1e-7) {
#ifdef COMPUTE_STATS
            nimproveo1++;
#endif
            bscore_cid = cscore;
            memcpy(&bsol[cid][0], &csol[0], ncsol * sizeof(int));
        }
    }
}

int nattempts2opt, naccept2opt, nimprove2opt;

inline void Do2Opt() {
    // Try to do a 2-opt move.
#ifdef COMPUTE_STATS
    nattempts2opt++;
#endif
    int wpozu = XOR128::rand() % NSEL;
    int dpidu = wdpid[wpozu];
    int pidu = dpidu >> 1;
    int pozu = cpoz[dpidu];

    int pidv = vec[pidu][XOR128::rand() % nvec[pidu]];
    int dpidv;
    if (pidu != pidv) dpidv = (pidv << 1) | (fast_rand & 1);
    else dpidv = dpidu ^ 1;
    int pozv = cpoz[dpidv];
    if (pozu > pozv) {
        int tmp = pozu; pozu = pozv; pozv = tmp;
    }
    unsigned int r = fast_rand;
    if (r & 1) {
        if (r & 2) {
            pozu++;
        } else {
            pozv--;
        }
    }

    if (pozu == pozv) return;

    int dpiduo = csol[pozu], dpidvo = csol[pozv] ^ 1;
    const auto& dall_dpiduo = dall[dpiduo];
    const auto& dall_dpidvo = dall[dpidvo];
    double dif = 0.0;
    if (pozu > 0) {
        int dpidu_prevo = csol[pozu - 1] ^ 1;
        const auto& dall_dpidu_prevo = dall[dpidu_prevo];
        int dx = dall_dpidu_prevo[0] - dall_dpidvo[0], dy = dall_dpidu_prevo[1] - dall_dpidvo[1];
        if (dx == 0 && dy == 0) return;
        dif += dsqrt[dx * dx + dy * dy];
        dx = dall_dpiduo[0] - dall_dpidu_prevo[0];
        dy = dall_dpiduo[1] - dall_dpidu_prevo[1];
        dif -= dsqrt[dx * dx + dy * dy];
    }
    if (pozv + 1 < ncsol) {
        int dpidv_nexto = csol[pozv + 1];
        const auto& dall_dpidv_nexto = dall[dpidv_nexto];
        int dx = dall_dpidv_nexto[0] - dall_dpiduo[0], dy = dall_dpidv_nexto[1] - dall_dpiduo[1];
        if (dx == 0 && dy == 0) return;
        dif += dsqrt[dx * dx + dy * dy];
        dx = dall_dpidvo[0] - dall_dpidv_nexto[0];
        dy = dall_dpidvo[1] - dall_dpidv_nexto[1];
        dif -= dsqrt[dx * dx + dy * dy];
    }
    if (dif < -1e-7 || (cscore + dif <= threshold * init_bscore_cid && Accept(dif))) {
#ifdef COMPUTE_STATS
        naccept2opt++;
#endif
        cscore += dif;
        reverse(&csol[pozu], &csol[pozv + 1]);
        for (int i = pozu; i <= pozv; i++) {
            csol[i] ^= 1;
            cpoz[csol[i] >> 1] = i;
        }
        auto& bscore_cid = bscore[cid];
        if (cscore < bscore_cid - 1e-7) {
#ifdef COMPUTE_STATS
            nimprove2opt++;
#endif
            bscore_cid = cscore;
            memcpy(&bsol[cid][0], &csol[0], ncsol * sizeof(int));
        }
        num_modified_elems += (pozv - pozu);
    }
}

void RecomputeNsel() {
    for (int i = 0; i < ncsol; i++) w[csol[i] >> 1] = 0.0;
    for (int i = 1; i < ncsol; i++) {
        int dpidio = csol[i];
        const auto& dall_dpidio = dall[dpidio];
        int prevdpido = csol[i - 1] ^ 1;
        const auto& dall_prevdpido = dall[prevdpido];
        int dx = dall_dpidio[0] - dall_prevdpido[0], dy = dall_dpidio[1] - dall_prevdpido[1];
        const auto& d = dsqrt[dx * dx + dy * dy];
        w[dpidio >> 1] += d;
        w[prevdpido >> 1] += d;
    }
    NSEL = QuickSelect(0, ncsol - 1) + 1;
}

int non_opt_cid[CMAX], num_non_opt_cid, icnt[CMAX], big_niter;
priority_queue<pair<double, int>> pq;

void ImproveSolution() {
    fast_rand_seed = 13U;
    XOR128::reset(13U);
    std::srand(13U);

    //while (!pq.empty()) pq.pop();

    num_modified_elems = num_non_opt_cid = 0;
    for (int i = 0; i < C; i++) {
        icnt[i] = 1;
        init_bscore[i] = bscore[i];
        if (npoz[i] > MAXELEMS) {
            non_opt_cid[num_non_opt_cid++] = i;
            //pq.push({1e30, i});
        }
    }

    if (num_non_opt_cid == 0) return;

    const unsigned int MAXNITER = 1000000;
    const double COEF_BEGIN = 2e-1;
    const double COEF_END = 1e1;
    const bool ALWAYS_RUN_2OPT = C <= 5;
    const double THRESHOLD_BEGIN = 0.2;
    const unsigned int niter_time_check_step = 100000;
    const unsigned int max_modified_elems_for_time_check = 900000;

    //const double THRESHOLD_END = 1e-2;//1e-2;
    //const double threshold_step = (THRESHOLD_END - THRESHOLD_BEGIN) / MAXNITER;

    sacoef[0] = COEF_BEGIN;
    if (C <= 5) {
        for (unsigned int niter = 1; niter <= MAXNITER; niter++)
            sacoef[niter] = COEF_BEGIN + (COEF_END - COEF_BEGIN) * niter / MAXNITER;
    } else {
        for (unsigned int niter = 1; niter <= MAXNITER; niter++)
            sacoef[niter] = COEF_BEGIN + (COEF_END - COEF_BEGIN) * pow(1.0 * niter / MAXNITER, 2.0);
    }
    
    big_niter = 0;
#ifdef COMPUTE_STATS
    nattempts2opt = naccept2opt = nimprove2opt = nattemptso1 = naccepto1 = nimproveo1 = nattemptso2 = nimproveo2 = nattemptskswap = nacceptkswap = nimprovekswap = 0;
#endif
    
    int icid = -1, ntime_checks = 0;
    while (GetTime() < TEND) {
        icid++; if (icid >= num_non_opt_cid) icid = 0;
        cid = non_opt_cid[icid];
        
        /*const auto& pqtop = pq.top();
        cid = pqtop.second;
        pq.pop();*/
        
        big_niter++;
        init_bscore_cid = init_bscore[cid];
        ncsol = nbsol[cid];
        memcpy(&csol[0], &bsol[cid][0], ncsol * sizeof(int));

        const auto& bscore_cid = bscore[cid];
        double bscore_cid_before = cscore = bscore[cid];
        
        for (int i = 0; i < ncsol; i++) {
            selected[i] = 0;
            int dpid = csol[i] >> 1;
            cpoz[dpid] = i;
            wdpid[i] = dpid;
        }
        selected_idx = 0;

        RecomputeNsel();

        const unsigned int QUICK_SELECT_NITER = ncsol <= 1024 ? 1023 : 2047;
        const unsigned int MINNITER_KSWAP = (ncsol >= 100 && C >= 4) ? 0 : MAXNITER + 1;
        const unsigned int MINNITER_O2 = (C <= 2 || ncsol <= 150) ? 0 : 500000;
        const unsigned int RPROB_O2 = (C <= 2 || ncsol <= 150) ? 100 : 50;
        const unsigned int RPROB_O1 = RPROB_O2 + 50;
        const unsigned int RPROB_KSWAP = RPROB_O1 + 50;//50;

        coef = COEF_BEGIN;

        const double THRESHOLD_END = (big_niter <= num_non_opt_cid || (C > 2 && ncsol > 25)) ? 1e-2 : 1.5e-2;
        const double threshold_step = (THRESHOLD_END - THRESHOLD_BEGIN) / MAXNITER;
        threshold = 1.0 + THRESHOLD_BEGIN;

        unsigned int niter = 0;
        unsigned int niter_time_check = niter_time_check_step;
        int pozu, pidu, dpidu, wpozu;
        
        while (niter < MAXNITER) {
            niter++;
            if (niter == niter_time_check || num_modified_elems >= max_modified_elems_for_time_check) {
                ntime_checks++;
                if (GetTime() > TEND) break;
                niter_time_check = niter + niter_time_check_step;
                num_modified_elems = 0;
            }

            if ((niter & QUICK_SELECT_NITER) == 0) RecomputeNsel();

            unsigned int xrand = XOR128::rand();
            const unsigned int rprob = xrand & 1023;
            
            /*if (((xrand >> 10) & 1023) < 2) {
                reverse(&csol[0], &csol[ncsol]);
                for (int i = 0; i < ncsol; i++) {
                    csol[i] ^= 1;
                    cpoz[csol[i] >> 1] = i;
                }
            }*/
            
            if (rprob < RPROB_O2) {
                if (niter >= MINNITER_O2) SwapAndReorientTwoDiagonals();
                else if (!ALWAYS_RUN_2OPT) {
                    if ((xrand >> 10) & 1) TryKSwapSolveOptimally2(2);
                    else Do2Opt();
                }
            }
            if (RPROB_O2 <= rprob && rprob < RPROB_O1) ReorientOneDiagonal();
            const bool run_kswap = niter >= MINNITER_KSWAP && RPROB_O1 <= rprob && rprob < RPROB_KSWAP;
            if (run_kswap) TryKSwapSolveOptimally2(2);
            if ((RPROB_O1 <= rprob && !run_kswap) || ALWAYS_RUN_2OPT) Do2Opt();
            threshold += threshold_step;
            coef = sacoef[niter];
        }
        /*
        auto& icnt_cid = icnt[cid];
        icnt_cid++;
        pq.push({(init_bscore_cid - bscore_cid) / icnt_cid, cid});
        */
    }
//#if defined(LOCAL) || defined(VISUALIZER)
//  fprintf(stderr, "big_niter=%d ntime_checks=%d\n", big_niter, ntime_checks);
//#ifdef COMPUTE_STATS
//  fprintf(stderr, "o2:%d/%d o1:%d/%d/%d 2opt:%d/%d/%d kswap:%d/%d/%d\n", big_niter, nattemptso2, nimproveo2, nattemptso1, naccepto1, nimproveo1, nattempts2opt, naccept2opt, nimprove2opt, nattemptskswap, nacceptkswap, nimprovekswap);
//#endif
//#endif
}

char stmp[128];

void AddPoint(int r, int c, vector<string>* ans) {
    sprintf(stmp, "%d %d", r, c);
    ans->push_back(stmp);
}

void PopulateFinalSolution(vector<string>* ans) {
    for (cid = 0; cid < C; cid++) {
        sprintf(stmp, "%c", cid + 'a');
        ans->push_back(stmp);
        const auto& bsol_cid = bsol[cid];
        const auto& nbsol_cid = nbsol[cid];
        for (int i = 0; i < nbsol_cid; i++) {
            int dpido = bsol_cid[i];
            const auto& dall_dpido = dall[dpido];
            int r1 = dall_dpido[0], c1 = dall_dpido[1];
            const auto& dall_dpidox = dall[dpido ^ 1];
            int r2 = dall_dpidox[0], c2 = dall_dpidox[1];
            AddPoint(r1, c1, ans);
            AddPoint(r2, c2, ans);
        }
    }
}

void Solve(const vector<string>& pattern, vector<string>* ans) {
    Init(pattern);
    FindInitialSolution();
    ImproveSolution();
    PopulateFinalSolution(ans);
}
}

class CrossStitch {
public:
    vector<string> embroider(const vector<string>& pattern) {
#ifdef VISUALIZER
        clock_t TSTART = clock();
#endif
        vector<string> ans;
        SOLVE::Solve(pattern, &ans);
#ifdef VISUALIZER
        double duration = (double) (clock() - TSTART) / CLOCKS_PER_SEC;
        fprintf(stderr, "TIME=%.3lf\n", duration);
#endif
        return ans;
    }
};

#ifdef VISUALIZER

char row[128];

int main() {
    int S;
    scanf("%d", &S);
    vector<string> pattern;
    for (int i = 0; i < S; ++i) {
        scanf("%s", row);
        pattern.push_back(row);
    }
    CrossStitch cs;
    vector<string> ret = cs.embroider(pattern);
    printf("%d\n", ret.size());
    for (int i = 0; i < (int)ret.size(); ++i)
        printf("%s\n", ret[i].c_str());
    fflush(stdout);
}

#endif

#ifdef LOCAL
char fname[128], row[NMAX + 5];
vector<string> pattern;
int N, C;

void ReadInput(int seed) {
    sprintf(fname, "cs\\cs-%d.txt", seed);
    freopen(fname, "r", stdin);
    scanf("%d", &N);
    assert(10 <= N && N <= 100);
    C = 0;
    pattern.clear();
    for (int i = 0; i < N; i++) {
        row[0] = 0;
        scanf("%s", row);
        pattern.push_back(row);
        assert(pattern[i].length() == N);
        for (int j = 0; j < N; j++) {
            if (pattern[i][j] == '.') continue;
            int c = pattern[i][j] - 'a' + 1;
            if (c > C) C = c;
        }
    }
}

vector<pair<int, int>> pts;
char done[NMAX][NMAX][2];
double W;

void MarkPoints() {
    if (pts.empty()) return;
    assert((pts.size() & 1) == 0);
    for (int i = 0; i + 1 < pts.size(); i += 2) {
        int r1 = pts[i].first, c1 = pts[i].second;
        assert(0 <= r1 && r1 <= N && 0 <= c1 && c1 <= N);
        int r2 = pts[i + 1].first, c2 = pts[i + 1].second;
        assert(0 <= r2 && r2 <= N && 0 <= c2 && c2 <= N);
        assert(abs(r2 - r1) == 1 && abs(c2 - c1) == 1);
        int r = min(r1, r2), c = min(c1, c2);
        if (r2 - r1 == c2 - c1) {
            if (done[r][c][0]) {
                fprintf(stderr, "already done: r=%d c=%d d=0\n", r, c);
            }
            assert(!done[r][c][0]);
            done[r][c][0] = 1;
        } else {
            if (done[r][c][1]) {
                fprintf(stderr, "already done: r=%d c=%d d=1\n", r, c);
            }
            assert(!done[r][c][1]);
            done[r][c][1] = 1;
        }
    }
    for (int i = 1; i + 1 < pts.size(); i += 2) {
        int r1 = pts[i].first, c1 = pts[i].second;
        int r2 = pts[i + 1].first, c2 = pts[i + 1].second;
        assert(r1 != r2 || c1 != c2);
        W += sqrt((r1 - r2) * (r1 - r2) + (c1 - c2) * (c1 - c2));       
    }
}

double ComputeScore(const vector<string>& ans) {
    W = 0.0;
    memset(done, 0, sizeof(done));
    pts.clear();
    char ch = -1;
    for (int k = 0; k < ans.size(); k++) {
        if (ans[k].length() == 1) {
            MarkPoints();
            pts.clear();
            ch = ans[k][0];
        } else {
            int row = -1, col = -1;
            sscanf(ans[k].c_str(), "%d %d", &row, &col);
            assert(0 <= row && row <= N && 0 <= col && col <= N);
            pts.push_back({row, col});
        }
    }
    MarkPoints();
    double sqrt2 = sqrt(2.0), L = 0.0;
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++)
            if (pattern[i][j] != '.') {
                assert(done[i][j][0]);
                assert(done[i][j][1]);
                L += 2.0 * sqrt2;
            }
    fprintf(stderr, "[ComputeScore] W=%.2lf L=%.2lf (W/L=%.3lf)\n", W, L, W / L);
    return 1e6 * pow(max(0.0, ((5.0 - W / L) / 5.0)), 3.0);
}

bool ShouldRunTest(int seed) {
//  return C > 5;
    return true;
}

#define SEEDMIN 1001
#define NUMSEEDS 50
double base_score[NUMSEEDS];

int main() {
    freopen("scores.txt", "r", stdin);
    for (int t = 0; t < NUMSEEDS; t++) {
        int sid = SEEDMIN + NUMSEEDS - 1, niter;
        double score;
        scanf("%d %lf %d", &sid, &score, &niter);
        assert(SEEDMIN <= sid && sid < SEEDMIN + NUMSEEDS);
        base_score[sid - SEEDMIN] = score;
    }
    freopen("tmp-scores.txt", "w", stdout);
    CrossStitch cs;
    int seedmin = 1001;
    int seedmax = 1050;
    double total_score = 0.0, total_base_score = 0.0;
    int numtests = 0;
    for (int seed = seedmin; seed <= seedmax; seed++) {
        ReadInput(seed);
        if (!ShouldRunTest(seed)) {
            printf("%d %.2lf\n", seed, base_score[seed - SEEDMIN]); fflush(stdout);
            continue;
        }
        clock_t TSTART = clock();
        vector<string> ans = cs.embroider(pattern);
        double duration = (double) (clock() - TSTART) / CLOCKS_PER_SEC;
        double score = ComputeScore(ans);
        numtests++;
        total_score += score;
        total_base_score += base_score[seed - SEEDMIN];
        fprintf(stderr, "### seed=%d: N=%d C=%d: sc=%.2lf(rsc=%.2lf) tsc=%.2lf(trsc=%.2lf) time=%.2lf\n\n", seed, N, C, score, 1e6 * score / base_score[seed - SEEDMIN], total_score / numtests, 1e6 * total_score / total_base_score, duration);
        printf("%d %.2lf %d\n", seed, score, SOLVE::big_niter); fflush(stdout);
    }
    return 0;
}
#endif

