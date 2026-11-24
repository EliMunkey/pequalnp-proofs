// Rebuild only the ancestors actually required to supply the specialized live
// signals.
struct Value {
  uint32_t need = 0;
  int8_t val = 2;
}; // 0,1,unknown
constexpr int PROJ = 320;
Value node[46][PROJ];
vector<array<int, 3>> pr;
void projSetup() {
  for (auto rt : restrictions) {
    if (__builtin_popcount(unsigned(rt[0])) > 2)
      continue;
    int lb = budget - rt[2] - __builtin_popcount(unsigned(rt[0]));
    pr.push_back({rt[0], rt[1], lb});
  }
  if (pr.size() > PROJ)
    exit(4);
  for (int i = 0; i < n; i++)
    for (size_t r = 0; r < pr.size(); r++)
      if (pr[r][0] >> i & 1)
        node[i][r].val = (pr[r][1] >> i) & 1;
}
void makeCone(int out, int a, int b, int ei, int ej, bool invert) {
  uint32_t own = 1u << (out - n);
  for (size_t q = 0; q < pr.size(); q++) {
    auto x = node[a][q], y = node[b][q];
    auto &z = node[out][q];
    if (x.val == 1 - ei || y.val == 1 - ej) {
      z = {0, (int8_t)invert};
    } else if (x.val == ei && y.val == ej) {
      z = {0, (int8_t)!invert};
    } else if (x.val == ei) {
      z = {y.need, 2};
    } else if (y.val == ej) {
      z = {x.need, 2};
    } else
      z = {x.need | y.need | own, 2};
  }
}
