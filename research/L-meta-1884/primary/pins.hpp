#include <fstream>
constexpr int GMAX = 128;
struct Flags {
  uint64_t z[GMAX], o[GMAX];
};
struct Slack {
  uint64_t b[4][GMAX];
};
vector<array<int, 3>> restrictions;
int groups = 0;
Flags sig[45] = {};
Slack rootSlack = {};
void setupPins(string mode) {
  ifstream file("pins-" + mode + ".txt");
  int m, v, b;
  while (file >> m >> v >> b) {
    int limit = budget - b - __builtin_popcount((unsigned)m);
    if (limit < 0) {
      cout << "smaller than restricted subproblem lower bound\n";
      exit(3);
    }
    if (limit < 16)
      restrictions.push_back({m, v, limit});
  }
  // Tightest restrictions first for early exits.
  stable_sort(restrictions.begin(), restrictions.end(),
              [](auto a, auto b) { return a[2] < b[2]; });
  groups = (restrictions.size() + 63) / 64;
  if (!groups || groups > GMAX) {
    cerr << "invalid number of pin checks " << groups << "\n";
    exit(2);
  }
  for (size_t q = 0; q < restrictions.size(); q++) {
    int g = q / 64;
    uint64_t bit = 1ULL << (q % 64);
    auto [mask, val, slack] = restrictions[q];
    for (int i = 0; i < n; i++)
      if (mask >> i & 1) {
        if (val >> i & 1)
          sig[i].o[g] |= bit;
        else
          sig[i].z[g] |= bit;
      }
    for (int i = 0; i < 4; i++)
      if (slack >> i & 1)
        rootSlack.b[i][g] |= bit;
  }
}
bool pinStep(const Flags &a, const Flags &b, int ei, int ej, int remove,
             bool invert, const Slack &from, Slack &to, Flags &t) {
  for (int g = 0; g < groups; g++) {
    const auto A = a.z[g] | a.o[g], B = b.z[g] | b.o[g];
    const auto ba = ei ? a.z[g] : a.o[g], bb = ej ? b.z[g] : b.o[g];
    const auto yes = (ei ? a.o[g] : a.z[g]) & (ej ? b.o[g] : b.z[g]),
               no = ba | bb;
    t.z[g] = invert ? yes : no;
    t.o[g] = invert ? no : yes;
    const uint64_t keepA = (remove & 1) ? 0 : A, keepB = (remove & 2) ? 0 : B;
    const uint64_t block = (ba & ~B) | (bb & ~A);
    const uint64_t one = keepA | keepB | block,
                   two = (keepA & keepB) | ((keepA | keepB) & block);
    const auto l0 = from.b[0][g], l1 = from.b[1][g], l2 = from.b[2][g],
               l3 = from.b[3][g];
    if ((one & ~(l0 | l1 | l2 | l3)) || (two & ~(l1 | l2 | l3)))
      return false;
    const auto b1 = one & ~l0, b2 = b1 & ~l1, b3 = b2 & ~l2;
    const auto o0 = l0 ^ one, o1 = l1 ^ b1, o2 = l2 ^ b2, o3 = l3 ^ b3;
    const auto c1 = two & ~o0, c2 = c1 & ~o1, c3 = c2 & ~o2;
    to.b[0][g] = o0 ^ two;
    to.b[1][g] = o1 ^ c1;
    to.b[2][g] = o2 ^ c2;
    to.b[3][g] = o3 ^ c3;
  }
  return true;
}
