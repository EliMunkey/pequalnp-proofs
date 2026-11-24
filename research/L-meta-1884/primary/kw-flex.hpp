// Each bit represents one target-positive / target-negative boundary pair.
constexpr int KM = 16;
struct KW {
  uint64_t p[KM] = {}, m[KM] = {};
};
KW kwSig[45];
int kwWords = 0;
void setupKW() {
  vector<int> ps, ms;
  for (int r = 0; r < rows; r++) {
    bool boundary = true;
    for (int i = 0; i < n; i++) {
      if (i == dvar)
        continue;
      if (labels[r] && (r >> i & 1) && labels[r ^ (1 << i)])
        boundary = false;
      if (!labels[r] && !(r >> i & 1) && !labels[r ^ (1 << i)])
        boundary = false;
    }
    if (boundary) {
      if (labels[r])
        ps.push_back(r);
      else
        ms.push_back(r);
    }
  }
  kwWords = (ps.size() * ms.size() + 63) / 64;
  if (kwWords > KM)
    exit(4);
  int q = 0;
  for (int p : ps)
    for (int m : ms) {
      int w = q / 64;
      auto bit = 1ULL << (q++ % 64);
      for (int i = 0; i < n; i++) {
        if (p >> i & 1)
          kwSig[i].p[w] |= bit;
        if (m >> i & 1)
          kwSig[i].m[w] |= bit;
      }
    }
}
