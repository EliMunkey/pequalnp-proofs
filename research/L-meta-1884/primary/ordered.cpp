// Exact AND/OR synthesis on the cofactor boundary. Primary input zero may be
// read in either polarity.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
int dvar = 0;
using U = uint64_t;
constexpr int W = 22;
int n = 10, rows = 1024, budget = 18, sym = 1, cap = 1500000;
vector<int> labels;
U desired = 0, allRows = 0;
uint64_t states = 0, hits = 0;
#include "pins.hpp"
#include "kw-flex.hpp"
#include "cone.hpp"
vector<U> functions;
unordered_map<U, int> ids;
struct Hash {
  size_t operator()(const vector<int> &v) const {
    size_t h = 1;
    for (auto x : v)
      h = (h ^ unsigned(x + 1)) * 0x9e3779b185ebca87ULL;
    return h;
  }
};
unordered_map<vector<int>, int, Hash> memo;
int getID(U a) {
  auto [it, ok] = ids.emplace(a, functions.size());
  if (ok)
    functions.push_back(a);
  return it->second;
}
struct Wire {
  int id, place;
  bool dual;
};
vector<array<int, 7>> trace;
bool rootPair[W][W] = {};
int firstFilter = -1;
uint64_t rootDone = 0;
void orbit(const vector<pair<int, int>> &e) {
  bool a[W][W] = {};
  for (auto [i, j] : e)
    a[i][j] = a[j][i] = true;
  vector<int> p(n);
  for (int i = 0; i < n; i++)
    p[i] = i;
  for (int i = 0; i < n; i++)
    for (int j = i + 1; j < n; j++)
      rootPair[i][j] = true;
  do {
    if (p[dvar] != dvar)
      continue;
    bool ok = true;
    for (int i = 0; ok && i < n; i++)
      for (int j = 0; j < i; j++)
        if (a[i][j] != a[p[i]][p[j]]) {
          ok = false;
          break;
        }
    if (ok)
      for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++) {
          pair<int, int> v = minmax(p[i], p[j]);
          if (v < pair<int, int>(i, j))
            rootPair[i][j] = false;
        }
  } while (next_permutation(p.begin(), p.end()));
}
bool dfs(const vector<Wire> &live, int spare, int depth, const Slack &sl,
         int minPair) {
  ++states;
  if ((states & 4194303) == 0)
    cerr << "states " << states << " root cases " << rootDone << "\n";
  const int k = live.size();
  if (k < 2 || depth >= budget)
    return false;
  for (size_t q = 0; q < pr.size(); q++) {
    uint32_t all = 0;
    int c = 0;
    for (auto a : live) {
      auto t = node[a.place][q];
      all |= t.need;
      c += (t.val != 2);
    }
    if (k - 1 + spare + __builtin_popcount(all) - c < pr[q][2])
      return false;
  }
  vector<int> key;
  for (auto a : live)
    key.push_back((a.id * 2 + a.dual) * 32 + a.place);
  sort(key.begin(), key.end());
  key.push_back(-1 - minPair);
  auto it = memo.find(key);
  if (it != memo.end() && it->second >= spare) {
    hits++;
    return false;
  }
  U one[KM], two[KM], sep[W][KM];
  for (int w = 0; w < kwWords; w++) {
    U a = 0, b = 0, c = 0;
    for (int q = 0; q < k; q++) {
      auto &v = kwSig[live[q].place];
      U s = v.p[w] & ~v.m[w];
      if (live[q].dual)
        s |= ~v.p[w] & v.m[w];
      sep[q][w] = s;
      c |= b & s;
      b |= a & s;
      a |= s;
    }
    one[w] = a & ~b;
    two[w] = b & ~c;
  }
  Slack sub;
  for (int i = 0; i < k; i++)
    for (int j = i + 1; j < k; j++) {
      if (!depth && sym && !rootPair[i][j])
        continue;
      auto x = live[i], y = live[j];
      const int ord = 32 * max(x.place, y.place) + min(x.place, y.place);
      if (ord < minPair)
        continue;
      for (int ri = 0; ri <= int(x.dual); ri++)
        for (int rj = 0; rj <= int(y.dual); rj++)
          for (int op = 0; op < 2; op++) {
            U a = functions[x.id] ^ (ri ? allRows : 0),
              b = functions[y.id] ^ (rj ? allRows : 0);
            U h = op ? (a | b) : (a & b);
            if (!h || h == allRows)
              continue;
            bool duplicate = false;
            for (auto v : live)
              if (h == functions[v.id] ||
                  (v.dual && h == (allRows ^ functions[v.id]))) {
                duplicate = true;
                break;
              }
            if (duplicate)
              continue;
            int fi = -1;
            int ei = op ? ri : !ri, ej = op ? rj : !rj;
            bool made = false;
            for (int remove : {3, 1, 2, 0}) {
              int cost = 2 - __builtin_popcount(unsigned(remove));
              if (cost > spare)
                continue;
              if (!depth && firstFilter != -1 &&
                  firstFilter != ((i * 16 + j) * 8 + ri * 4 + rj * 2 + op))
                continue;
              bool di = remove & 1, dj = remove & 2, ok = true;
              auto &dest = kwSig[n + depth];
              for (int w = 0; w < kwWords; w++) {
                auto &u = kwSig[x.place], &v = kwSig[y.place];
                U p = (ei ? u.p[w] : ~u.p[w]) & (ej ? v.p[w] : ~v.p[w]),
                  m = (ei ? u.m[w] : ~u.m[w]) & (ej ? v.m[w] : ~v.m[w]);
                if (op) {
                  p = ~p;
                  m = ~m;
                }
                U lost = one[w] & ((di ? sep[i][w] : 0) | (dj ? sep[j][w] : 0));
                if (di && dj)
                  lost |= two[w] & sep[i][w] & sep[j][w];
                if (lost & ~(p & ~m)) {
                  ok = false;
                  break;
                }
                dest.p[w] = p;
                dest.m[w] = m;
              }
              if (!ok || !pinStep(sig[x.place], sig[y.place], ei, ej, remove,
                                  op, sl, sub, sig[n + depth]))
                continue;
              if (!made) {
                makeCone(n + depth, x.place, y.place, ei, ej, op);
                made = true;
              }
              if (fi == -1)
                fi = getID(h);
              trace.push_back(
                  {x.place, y.place, ri, rj, op, n + depth, remove});
              if (h == desired)
                return true;
              vector<Wire> next;
              next.reserve(k + 1);
              for (int q = 0; q < k; q++)
                if (!(di && q == i) && !(dj && q == j))
                  next.push_back(live[q]);
              next.push_back({fi, n + depth, false});
              if (dfs(next, spare - cost, depth + 1, sub, depth == 0 ? 0 : ord))
                return true;
              trace.pop_back();
              if (!depth)
                ++rootDone;
            }
          }
    }
  if ((int)memo.size() < cap)
    memo[key] = max(memo[key], spare);
  return false;
}
int main(int argc, char **argv) {
  dvar = argc > 5 ? stoi(argv[5]) : 0;
  string mode = argc > 2 ? argv[2] : "petersen";
  budget = argc > 1 ? atoi(argv[1]) : 18;
  sym = argc > 3 ? atoi(argv[3]) : 1;
  firstFilter = argc > 4 ? atoi(argv[4]) : -1;
  vector<pair<int, int>> e = {{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 0},
                              {0, 5}, {1, 6}, {2, 7}, {3, 8}, {4, 9},
                              {5, 7}, {7, 9}, {9, 6}, {6, 8}, {8, 5}};
  if (mode == "deleted" || mode.rfind("delmask", 0) == 0) {
    int gone = mode == "deleted" ? 1 : stoi(mode.substr(7));
    int rename[10];
    n = 0;
    for (int i = 0; i < 10; i++)
      if (!(gone >> i & 1))
        rename[i] = n++;
    vector<pair<int, int>> ne;
    for (auto [i, j] : e)
      if (!(gone >> i & 1) && !(gone >> j & 1))
        ne.emplace_back(rename[i], rename[j]);
    e = ne;
  }
  rows = 1 << n;
  for (int r = 0; r < rows; r++) {
    bool v = false;
    for (auto [i, j] : e)
      v |= (r >> i) & (r >> j) & 1;
    labels.push_back(v);
  }
  vector<int> bs;
  for (int r = 0; r < rows; r++) {
    bool b = true;
    for (int i = 0; i < n; i++)
      if (i != dvar && bool(r & (1 << i)) == bool(labels[r]) &&
          labels[r ^ (1 << i)] == labels[r])
        b = false;
    if (b)
      bs.push_back(r);
  }
  if (bs.size() >= 64)
    return 3;
  allRows = (1ULL << bs.size()) - 1;
  vector<Wire> live;
  for (int i = 0; i < n; i++) {
    U f = 0;
    for (int j = 0; j < (int)bs.size(); j++)
      if (bs[j] >> i & 1)
        f |= 1ULL << j;
    live.push_back({getID(f), i, i == dvar});
  }
  for (int j = 0; j < (int)bs.size(); j++)
    if (labels[bs[j]])
      desired |= 1ULL << j;
  setupKW();
  setupPins(mode);
  projSetup();
  orbit(e);
  auto start = chrono::steady_clock::now();
  bool found = dfs(live, budget - (n - 1), 0, rootSlack, 0);
  cout << mode << " budget " << budget << " found " << found << " states "
       << states << " memo_hits " << hits << " functions " << ids.size()
       << " boundary " << bs.size() << " seconds "
       << chrono::duration<double>(chrono::steady_clock::now() - start).count()
       << "\n";
  if (found)
    for (auto step : trace) {
      for (auto a : step)
        cout << a << " ";
      cout << "\n";
    }
}
