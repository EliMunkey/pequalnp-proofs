// Exhaustive AND/OR replay. On each slice fixing the only negative input rail,
// all signals are monotone. A physical wire carries its actual Boolean truth
// table.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <numeric>
#include <string>
#include <unordered_map>
#include <vector>
#ifdef __aarch64__
#include <arm_neon.h>
#endif
using namespace std;
using U = uint64_t;
constexpr int MAX = 22, NP = 8192, NC = 96;
struct Pin {
  int m, v, L;
};
struct Wire {
  U truth;
  int src;
};
using Key = vector<U>;
struct H {
  size_t operator()(const Key &k) const {
    U h = 0x9e3779b97f4a7c15ULL;
    for (U x : k) {
      x ^= x >> 23;
      x *= 0x2127599bf4325c37ULL;
      h ^= x ^ (x >> 47);
      h *= 0x9e3779b185ebca87ULL;
    }
    return h;
  }
};
int adj[10] = {50, 69, 138, 276, 521, 385, 770, 548, 104, 208};
vector<int> vs, brows;
vector<Pin> pins;
int cubicMode = 1;
int n, ng, nr, ngroups, dual, cutpins = 10, rootrestrict = 1,
                              cachecap = 1200000;
U goal, mask;
uint64_t nodes = 0, hits = 0, stopped = 0, conecut = 0;
bool orbit[MAX][MAX] = {};
alignas(16) uint8_t flags[45][NP];
alignas(16) int8_t slack[MAX][NP];
uint32_t cones[45][NC];
uint16_t rowcode[MAX][64];
unordered_map<Key, uint8_t, H> memo;
U orig[MAX];
uint64_t dominated = 0, incoherent = 0;
array<int, 6> trace[MAX], foundTrace[MAX];
vector<U> staticOneGate;
unordered_map<U, bool> dominatedInitially;
int foundSize = -1;
chrono::steady_clock::time_point started;
int pop(U x) { return __builtin_popcountll(x); }
int tz(U x) { return __builtin_ctzll(x); }
void geometry(int keep) {
  for (int i = 0; i < 10; i++)
    if (keep >> i & 1)
      vs.push_back(i);
  n = vs.size();
  vector<int> lab(1 << n);
  for (int r = 0; r < (1 << n); r++) {
    int old = 0;
    for (int i = 0; i < n; i++)
      if (r >> i & 1)
        old |= 1 << vs[i];
    for (int v : vs)
      if ((old >> v & 1) && (adj[v] & old)) {
        lab[r] = 1;
        break;
      }
  }
  for (int r = 0; r < (1 << n); r++)
    if ((r & 42) == 42 || (cubicMode == 2 && (r & 261) == 261))
      lab[r] = 1;
  for (int r = 0; r < (1 << n); r++) {
    bool need = true;
    for (int i = 0; i < n; i++)
      if (i != dual && int(bool(r & (1 << i))) == lab[r] &&
          lab[r ^ (1 << i)] == lab[r])
        need = false;
    if (need && r != 42 && r != 261) {
      if (lab[r])
        goal |= U(1) << brows.size();
      brows.push_back(r);
    }
  }
  nr = brows.size();
  if (nr > 63) {
    cerr << "too many boundary rows\n";
    exit(4);
  }
  mask = (U(1) << nr) - 1;
  vector<int> perm(n);
  iota(perm.begin(), perm.end(), 0);
  for (int i = 0; i < n; i++)
    for (int j = i + 1; j < n; j++)
      orbit[i][j] = true;
  do {
    if (dual >= 0 && perm[dual] != dual)
      continue;
    bool is = true;
    for (int i = 1; i < n && is; i++)
      for (int j = 0; j < i; j++)
        if (((adj[vs[i]] >> vs[j]) ^ (adj[vs[perm[i]]] >> vs[perm[j]])) & 1) {
          is = false;
          break;
        }
    if (is) {
      int t = 0, u = 0;
      for (int i = 0; i < n; i++) {
        if (42 >> i & 1)
          t |= 1 << perm[i];
        if (261 >> i & 1)
          u |= 1 << perm[i];
      }
      if (t != 42 && !(cubicMode == 2 && t == 261 && u == 42))
        is = false;
    }
    if (is)
      for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
          if (pair<int, int>(minmax(perm[i], perm[j])) < pair<int, int>(i, j))
            orbit[i][j] = false;
  } while (next_permutation(perm.begin(), perm.end()));
}
bool pin(int depth, int i, int j, int wantA, int wantB, int opposite,
         int keep) {
  const auto *as = flags[i], *bs = flags[j];
  auto *out = flags[n + depth];
  const int ka = bool(keep & 1), kb = bool(keep & 2), blockA = 2 - wantA,
            blockB = 2 - wantB;
  auto scalar = [&](int q) {
    int a = as[q], b = bs[q];
    bool blocked = a == blockA || b == blockB;
    int val = blocked ? 1 : (a && b) ? 2 : 0;
    int debit = ka * bool(a) + kb * bool(b) + (blocked && ((!a) != (!b)));
    int remain = slack[depth][q] - debit;
    slack[depth + 1][q] = remain;
    out[q] = (opposite && val) ? 3 - val : val;
    return remain >= 0;
  };
  int m = pins.size(), q = 0;
  for (; q < min(m, 16); q++)
    if (!scalar(q))
      return false;
#ifdef __aarch64__
  const auto z = vdupq_n_u8(0), opp = vdupq_n_u8(opposite), one = vdupq_n_u8(1);
  for (; q + 16 <= m; q += 16) {
    auto a = vld1q_u8(as + q), b = vld1q_u8(bs + q);
    auto A = vcgtq_u8(a, z), B = vcgtq_u8(b, z);
    auto block = vorrq_u8(vceqq_u8(a, vdupq_n_u8(blockA)),
                          vceqq_u8(b, vdupq_n_u8(blockB)));
    auto spend = vandq_u8(one, vandq_u8(block, veorq_u8(A, B)));
    if (ka)
      spend = vsubq_u8(spend, A);
    if (kb)
      spend = vsubq_u8(spend, B);
    auto remain =
        vsubq_s8(vld1q_s8(slack[depth] + q), vreinterpretq_s8_u8(spend));
    if (vminvq_s8(remain) < 0)
      return false;
    vst1q_s8(slack[depth + 1] + q, remain);
    // A blocked gate has raw value zero. Both active literals set, with no
    // block, have value one.
    auto known = vorrq_u8(block, vandq_u8(A, B));
    auto val = vandq_u8(
        known, vaddq_u8(one, veorq_u8(opp, vandq_u8(one, vmvnq_u8(block)))));
    vst1q_u8(out + q, val);
  }
#endif
  for (; q < m; q++)
    if (!scalar(q))
      return false;
  return true;
}
bool cone(int d, const vector<Wire> &live, int i, int j, int wantA, int wantB,
          int keep) {
  for (int q = 0; q < cutpins; q++) {
    auto a = flags[live[i].src][q], b = flags[live[j].src][q],
         o = flags[n + d][q];
    auto x = cones[live[i].src][q], y = cones[live[j].src][q];
    uint32_t h = o ? 0 : (a ? y : b ? x : (x | y | (uint32_t(1) << d)));
    cones[n + d][q] = h;
    int fixed = bool(o);
    for (int s = 0; s < (int)live.size(); s++)
      if ((s != i || (keep & 1)) && (s != j || (keep & 2))) {
        fixed += bool(flags[live[s].src][q]);
        h |= cones[live[s].src][q];
      }
    // h is the union of retained nontrivial gate ancestry, hence an upper bound
    // on gates needed to reconstruct all current live signals in the restricted
    // circuit.
    if (pop(h) + (ng - d - 1) - fixed < pins[q].L)
      return false;
  }
  return true;
}
bool dfs(const vector<Wire> &live, int d, int orderFloor) {
  auto &row = rowcode[d];
  int L = live.size(), remaining = ng - d;
  nodes++;
  if ((nodes & 0x7fffff) == 0)
    cerr << "visited " << nodes << " cache=" << memo.size() << " elapsed="
         << chrono::duration<double>(chrono::steady_clock::now() - started)
                .count()
         << "\n";
  for (auto w : live)
    if (w.truth == goal) {
      copy_n(trace, d, foundTrace);
      foundSize = d;
      return true;
    }
  if (L < 2 || remaining < L - 1 || remaining == 0)
    return false;
  Key key;
  for (auto w : live)
    key.push_back((w.truth << 6) + w.src);
  sort(key.begin(), key.end());
  key.push_back(orderFloor);
  if (auto it = memo.find(key); it != memo.end() && it->second >= remaining) {
    hits++;
    return false;
  }
  // Each opposite boundary pair imposes an oriented obligation on live rails.
  // If only one/two rails separate the pair, retiring all of them obliges the
  // new output to contain its positive row and exclude its negative row.
  // Combine obligations as masks.
  U soloP[MAX] = {}, soloN[MAX] = {}, duoP[MAX][MAX] = {}, duoN[MAX][MAX] = {};
  unsigned dualbit = 0;
  for (int q = 0; q < L; q++)
    if (live[q].src == dual)
      dualbit = 1u << q;
  for (U ps = goal; ps; ps &= ps - 1) {
    int p = tz(ps);
    int code = row[p];
    U pbit = U(1) << p;
    for (U ns = mask ^ goal; ns; ns &= ns - 1) {
      int m = tz(ns);
      unsigned other = row[m];
      unsigned sep = (code & ~other) | ((code ^ other) & dualbit);
      if (!sep)
        return false;
      unsigned rem = sep & (sep - 1);
      int i = __builtin_ctz(sep);
      if (!rem) {
        soloP[i] |= pbit;
        soloN[i] |= U(1) << m;
      } else if (!(rem & (rem - 1))) {
        int j = __builtin_ctz(rem);
        duoP[i][j] |= pbit;
        duoN[i][j] |= U(1) << m;
      }
    }
  }
  for (int i = 0; i < L; i++)
    for (int j = i + 1; j < L; j++) {
      if (d == 0 && rootrestrict && !orbit[i][j])
        continue;
      auto a = live[i], b = live[j];
      int order = max(a.src, b.src) * 32 + min(a.src, b.src);
      if (order < orderFloor)
        continue;
      for (int sa = 0; sa <= int(a.src == dual); sa++)
        for (int sb = 0; sb <= int(b.src == dual); sb++) {
          U x = a.truth ^ (sa ? mask : 0), y = b.truth ^ (sb ? mask : 0);
          for (int op = 0; op < 2; op++) {
            U f = op ? x | y : x & y;
            if (!f || f == mask)
              continue;
            // A live rail dominates f iff it agrees with the desired label at
            // every row on which f agrees.
            U correct = (~(f ^ goal)) & mask, neg = mask ^ goal;
            auto better = [&](U w) { return !(correct & (w ^ goal)); };
            bool drop = better(0) || better(mask);
            for (int u = 0; !drop && u < n; u++)
              drop = better(orig[u]) || (u == dual && better(orig[u] ^ mask));
            for (auto w : live)
              if (!drop && better(w.truth))
                drop = true;
            if (!drop) {
              auto it = dominatedInitially.find(f);
              if (it != dominatedInitially.end())
                drop = it->second;
              else {
                for (U w : staticOneGate)
                  if (w != f && better(w)) {
                    drop = true;
                    break;
                  }
                dominatedInitially.emplace(f, drop);
              }
            }
            if (drop) {
              dominated++;
              continue;
            }
            // An ordinary wire strictly dominated by this new one has no future
            // use in the maximum-total-operand-agreement witness among minimum
            // circuits.
            unsigned mustRetire = 0;
            for (int s = 0; s < L; s++)
              if (live[s].src != dual) {
                U w = live[s].truth;
                if (w != f && !((~(w ^ goal) & mask) & ~correct))
                  mustRetire |= 1u << s;
              }
            if (mustRetire & ~((1u << i) | (1u << j))) {
              incoherent++;
              continue;
            }
            for (int keep = 0; keep < 4; keep++) {
              int nextN = L - 1 + pop(keep);
              if (remaining - 1 < nextN - 1)
                continue;
              bool ka = keep & 1, kb = keep & 2;
              if ((ka && (mustRetire & (1u << i))) ||
                  (kb && (mustRetire & (1u << j)))) {
                incoherent++;
                continue;
              }
              U pos = (ka ? 0 : soloP[i]) | (kb ? 0 : soloP[j]) |
                      (!keep ? duoP[i][j] : 0);
              U neg = (ka ? 0 : soloN[i]) | (kb ? 0 : soloN[j]) |
                      (!keep ? duoN[i][j] : 0);
              if ((pos & ~f) || (neg & f))
                continue;
              int wa = 1 ^ sa ^ op, wb = 1 ^ sb ^ op;
              if (!pin(d, a.src, b.src, wa, wb, op, keep)) {
                stopped++;
                continue;
              }
              if (!cone(d, live, i, j, wa, wb, keep)) {
                conecut++;
                continue;
              }
              vector<Wire> next;
              for (int s = 0; s < L; s++)
                if ((s != i || ka) && (s != j || kb))
                  next.push_back(live[s]);
              int at = next.size();
              next.push_back({f, n + d});
              for (int rr = 0; rr < nr; rr++) {
                int z = row[rr];
                if (!kb) {
                  int low = (1 << j) - 1;
                  z = (z & low) | ((z >> 1) & ~low);
                }
                if (!ka) {
                  int low = (1 << i) - 1;
                  z = (z & low) | ((z >> 1) & ~low);
                }
                rowcode[d + 1][rr] = z | (int((f >> rr) & 1) << at);
              }
              trace[d] = {a.src, b.src, sa, sb, op, keep};
              if (dfs(next, d + 1, d ? order : 0))
                return true;
            }
          }
        }
    }
  if ((int)memo.size() < cachecap) {
    auto &v = memo[key];
    v = max<int>(v, remaining);
  }
  return false;
}
int main(int ac, char **av) {
  if (ac < 5)
    return 2;
  int keep = stoi(av[1]);
  ng = stoi(av[2]);
  dual = stoi(av[3]);
  if (ac > 5)
    cutpins = stoi(av[5]);
  if (ac > 6)
    rootrestrict = stoi(av[6]);
  if (ac > 7)
    cachecap = stoi(av[7]);
  if (ac > 8)
    cubicMode = stoi(av[8]);
  geometry(keep);
  if (string(av[4]) != "-") {
    ifstream fin(av[4]);
    if (!fin)
      return 3;
    Pin p;
    while (fin >> p.m >> p.v >> p.L)
      pins.push_back(p);
  }
  sort(pins.begin(), pins.end(), [](auto a, auto b) {
    return pair(a.L + pop(a.m), a.L) > pair(b.L + pop(b.m), b.L);
  });
  if (pins.size() > NP || cutpins > NC)
    return 5;
  cutpins = min(cutpins, int(pins.size()));
  for (int q = 0; q < (int)pins.size(); q++) {
    auto p = pins[q];
    int rem = ng - p.L - pop(p.m);
    if (rem < 0) {
      cout << "mask=" << keep << " result=UNSAT by initial pin\n";
      return 0;
    }
    slack[0][q] = rem;
    for (int s = 0; s < n; s++)
      if (p.m >> s & 1)
        flags[s][q] = 1 + (p.v >> s & 1);
  }
  vector<Wire> live;
  for (int i = 0; i < n; i++) {
    U f = 0;
    for (int q = 0; q < nr; q++)
      if (brows[q] >> i & 1)
        f |= U(1) << q;
    orig[i] = f;
    live.push_back({f, i});
  }
  for (int q = 0; q < nr; q++)
    rowcode[0][q] = brows[q];
  vector<U> primary;
  for (int s = 0; s < n; s++) {
    primary.push_back(orig[s]);
    if (s == dual)
      primary.push_back(orig[s] ^ mask);
  }
  for (U a : primary)
    for (U b : primary) {
      staticOneGate.push_back(a & b);
      staticOneGate.push_back(a | b);
    }
  sort(staticOneGate.begin(), staticOneGate.end());
  staticOneGate.erase(unique(staticOneGate.begin(), staticOneGate.end()),
                      staticOneGate.end());
  started = chrono::steady_clock::now();
  bool found = dfs(live, 0, 0);
  cout
      << "mask=" << keep << " k=" << ng << " dual=" << dual
      << " boundary=" << nr << " pins=" << pins.size() << " cone=" << cutpins
      << " result=" << (found ? "SAT" : "UNSAT") << " nodes=" << nodes
      << " memo=" << hits << " pin=" << stopped << " cone=" << conecut
      << " dominated=" << dominated << " retire=" << incoherent << " sec="
      << chrono::duration<double>(chrono::steady_clock::now() - started).count()
      << "\n";
  if (found)
    for (int d = 0; d < foundSize; d++) {
      for (auto v : foundTrace[d])
        cout << v << ' ';
      cout << '\n';
    }
}
