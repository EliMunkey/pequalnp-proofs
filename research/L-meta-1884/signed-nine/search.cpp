// Exhaustive circuit synthesis over U2. Gate outputs and wires may be
// complemented for free. A wire is retired at its last use. Every pair of
// opposite target labels must remain distinguishable.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using namespace std;
using Table = array<uint64_t, 16>;
struct TableHash {
  size_t operator()(const Table &a) const {
    size_t h = 17;
    for (auto v : a)
      h = (h ^ (v + (v >> 33))) * 0x9e3779b185ebca87ULL;
    return h;
  }
};
struct VecHash {
  size_t operator()(const vector<int> &a) const {
    size_t h = 1;
    for (int v : a)
      h = (h ^ unsigned(v + 1)) * 0x9e3779b185ebca87ULL;
    return h;
  }
};
int n = 10, rows = 1024, budget = 14, target, sym = 1;
constexpr int W = 22;
int maxMemo = 1000000;
uint64_t states = 0, candidates = 0, hits = 0, countByDepth[32] = {};
vector<Table> tables;
unordered_map<Table, int, TableHash> intern;
unordered_map<vector<int>, int, VecHash> completed;
vector<int> negatives, labels;
vector<array<int, 6>> trail;
#include "../primary/pins.hpp"
#include "../primary/cone.hpp"
bool rootPair[W][W] = {};
void markPairs(const vector<pair<int, int>> &edges) {
  bool A[W][W] = {};
  for (auto [i, j] : edges)
    A[i][j] = A[j][i] = true;
  vector<int> p(n);
  for (int i = 0; i < n; i++)
    p[i] = i;
  for (int i = 0; i < n; i++)
    for (int j = i + 1; j < n; j++)
      rootPair[i][j] = true;
  do {
    bool ok = true;
    for (int i = 0; i < n && ok; i++)
      for (int j = 0; j < i; j++)
        if (A[i][j] != A[p[i]][p[j]]) {
          ok = false;
          break;
        }
    if (ok)
      for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++) {
          pair<int, int> q = minmax(p[i], p[j]);
          if (q < pair<int, int>(i, j))
            rootPair[i][j] = false;
        }
  } while (next_permutation(p.begin(), p.end()));
}

int id(const Table &t) {
  auto [it, ok] = intern.emplace(t, (int)tables.size());
  if (ok)
    tables.push_back(t);
  return it->second;
}
bool dfs(const vector<int> &live, const vector<int> &map, int copies, int depth,
         const vector<int> &sources, const Slack &slack) {
  states++;
  countByDepth[depth]++;
  if ((states & 1048575) == 0)
    cerr << "progress states " << states << " stored " << completed.size()
         << " tables " << tables.size() << "\n";
  const int k = live.size();
  if (find(live.begin(), live.end(), target) != live.end())
    return true;
  if (k < 2 || depth >= budget)
    return false;
  // Specialize the prefix separately for each cofactor. Rebuild the union of
  // ancestors needed by all surviving signals, and save every constant live
  // wire.
  for (size_t q = 0; q < pr.size(); ++q) {
    uint32_t dep = 0;
    int constants = 0;
    for (auto v : sources) {
      auto x = node[v][q];
      dep |= x.need;
      constants += (x.val != 2);
    }
    if (budget - depth + __builtin_popcount(dep) - constants < pr[q][2])
      return false;
  }
  // Same live functions, in any order, give the same possible futures. Keep the
  // largest exhausted budget.
  vector<int> key = live;
  sort(key.begin(), key.end());
  auto prev = completed.find(key);
  if (prev != completed.end() && prev->second >= copies) {
    hits++;
    return false;
  }
  Slack subSlack;
  vector<int8_t> classOf(1 << k, -1);
  for (int r = 0; r < rows; r++)
    classOf[map[r]] = labels[r];
  const unsigned full = (1u << k) - 1;
  unsigned all[W], any[W] = {};
  fill(all, all + k, full);
  uint8_t parity[W][W] = {};
  for (int raw : negatives) {
    const int u = map[raw];
    for (int i = 0; i < k; i++) {
      int v = u ^ (1 << i);
      if (classOf[v] == 1) {
        all[i] &= u;
        any[i] |= u;
      }
      for (int j = 0; j < i; j++)
        if (classOf[v ^ (1 << j)] == 1)
          parity[j][i] |= 1u << (((u >> i) ^ (u >> j)) & 1);
    }
  }
  for (int spend = 0; spend <= min(2, copies); spend++) {
    for (int i = 0; i < k; i++)
      for (int j = i + 1; j < k; j++) {
        if (depth == 0 && sym && !rootPair[i][j])
          continue;
        for (int bits = 0; bits < 4; bits++) {
          const int ei = bits & 1, ej = bits >> 1;
          bool canI = ej ? (all[i] >> j) & 1 : !((any[i] >> j) & 1);
          bool canJ = ei ? (all[j] >> i) & 1 : !((any[j] >> i) & 1);
          if (spend == 0 &&
              !(canI && canJ && !(parity[i][j] & (1 << (1 ^ ei ^ ej)))))
            continue;
          if (spend == 1 && !canI && !canJ)
            continue;
          Table t = {};
          for (int w = 0; w < (rows + 63) / 64; w++) {
            auto a = tables[live[i]][w], b = tables[live[j]][w];
            t[w] = (ei ? a : ~a) & (ej ? b : ~b);
          }
          bool invert = t[0] & 1;
          if (invert)
            for (int w = 0; w < (rows + 63) / 64; w++)
              t[w] = ~t[w];
          if (rows < 64)
            t[0] &= ((1ULL << rows) - 1);
          if (all_of(t.begin(), t.end(), [](auto w) { return w == 0; }))
            continue;
          if (find_if(live.begin(), live.end(),
                      [&](auto v) { return tables[v] == t; }) != live.end())
            continue;
          int fresh = -1;
          for (int remove : {3, 1, 2, 0}) {
            const bool di = remove & 1, dj = remove & 2;
            if (2 - int(di) - int(dj) != spend || (di && !canI) ||
                (dj && !canJ))
              continue;
            if (!pinStep(sig[sources[i]], sig[sources[j]], ei, ej, remove,
                         invert, slack, subSlack, sig[n + depth]))
              continue;
            if (fresh < 0) {
              fresh = id(t);
              makeCone(n + depth, sources[i], sources[j], ei, ej, invert);
            }
            candidates++;
            vector<int> next, ns;
            for (int q = 0; q < k; q++)
              if (!(q == i && di) && !(q == j && dj)) {
                next.push_back(live[q]);
                ns.push_back(sources[q]);
              }
            const int output = next.size();
            next.push_back(fresh);
            ns.push_back(n + depth);
            if (fresh == target) {
              trail.push_back({live[i], live[j], ei, ej, fresh, remove});
              return true;
            }
            vector<int> nm(rows);
            for (int r = 0; r < rows; r++) {
              int x = map[r];
              if (dj)
                x = (x & ((1 << j) - 1)) | ((x >> (j + 1)) << j);
              if (di)
                x = (x & ((1 << i) - 1)) | ((x >> (i + 1)) << i);
              nm[r] = x | (((t[r >> 6] >> (r & 63)) & 1) << output);
            }
            trail.push_back({live[i], live[j], ei, ej, fresh, remove});
            if (dfs(next, nm, copies - spend, depth + 1, ns, subSlack))
              return true;
            trail.pop_back();
          }
        }
      }
  }
  if ((int)completed.size() < maxMemo)
    completed[key] = max(completed[key], copies);
  return false;
}
int main(int argc, char **argv) {
  if (argc < 3)
    return 2;
  budget = atoi(argv[1]);
  string mode = argv[2];
  if (argc > 3)
    sym = atoi(argv[3]);
  if (argc > 4)
    maxMemo = atoi(argv[4]);
  vector<pair<int, int>> E = {{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 0},
                              {0, 5}, {1, 6}, {2, 7}, {3, 8}, {4, 9},
                              {5, 7}, {7, 9}, {9, 6}, {6, 8}, {8, 5}};
  if (mode == "cycle") {
    n = 6;
    E = {{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 5}, {5, 0}};
  }
  if (mode == "path") {
    n = 4;
    E = {{0, 1}, {1, 2}, {2, 3}};
  }
  if (mode == "fivecycle") {
    n = 5;
    E = {{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 0}};
  }
  if (mode == "deleted") {
    n = 9;
    vector<pair<int, int>> e;
    for (auto [i, j] : E)
      if (i && j)
        e.emplace_back(i - 1, j - 1);
    E = e;
  }
  if (mode.rfind("delmask", 0) == 0) {
    const int gone = stoi(mode.substr(7));
    vector<pair<int, int>> remain;
    int rename[10];
    n = 0;
    for (int i = 0; i < 10; i++)
      if (!(gone >> i & 1))
        rename[i] = n++;
    for (auto [i, j] : E)
      if (!(gone >> i & 1) && !(gone >> j & 1))
        remain.emplace_back(rename[i], rename[j]);
    E = remain;
  }
  rows = 1 << n;
  vector<int> map(rows), live;
  Table f = {};
  for (int i = 0; i < n; i++) {
    Table t = {};
    for (int r = 0; r < rows; r++)
      if (r >> i & 1)
        t[r >> 6] |= 1ULL << (r & 63);
    live.push_back(id(t));
  }
  for (int r = 0; r < rows; r++) {
    map[r] = r;
    bool yes = false;
    for (auto [a, b] : E)
      yes |= (r >> a) & (r >> b) & 1;
    labels.push_back(yes);
    if (yes)
      f[r >> 6] |= 1ULL << (r & 63);
    else
      negatives.push_back(r);
  }
  target = id(f);
  if (2 * n > 2 * W || budget > 20 || budget < n - 1)
    return 2;
  auto t = chrono::steady_clock::now();
  markPairs(E);
  setupPins(mode);
  projSetup();
  bool found = dfs(live, map, budget - (n - 1), 0, live, rootSlack);
  cout << mode << " gates " << budget << " sym " << sym << " found " << found
       << " states " << states << " branches " << candidates << " memo_hits "
       << hits << " tables " << tables.size() << " seconds "
       << chrono::duration<double>(chrono::steady_clock::now() - t).count()
       << "\n";
  if (found)
    for (auto g : trail) {
      for (int v : g)
        cout << v << " ";
      cout << "\n";
    }
}
