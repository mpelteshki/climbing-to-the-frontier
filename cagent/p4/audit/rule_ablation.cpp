#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <set>
#include <string>
#include <vector>

// Exact occurrence search. Pair and triple constraints are precomputed;
// --strong only enables the three proved early feasibility conditions.
// Complete-tuple conditions are identical in both modes.
struct Bits {
  std::array<uint64_t, 4> w{};
  void set(int i) { w[i / 64] |= uint64_t(1) << (i % 64); }
  bool test(int i) const { return (w[i / 64] >> (i % 64)) & 1; }
  bool none() const { return !(w[0] | w[1] | w[2] | w[3]); }
  Bits& operator&=(const Bits& other) {
    for (int j = 0; j < 4; ++j) w[j] &= other.w[j];
    return *this;
  }
  Bits operator&(const Bits& other) const {
    Bits result = *this;
    return result &= other;
  }
  int next(int i) const {
    int block = i / 64;
    if (block >= 4) return 256;
    uint64_t bits = w[block] & (~uint64_t(0) << (i % 64));
    while (true) {
      if (bits) return block * 64 + __builtin_ctzll(bits);
      if (++block >= 4) return 256;
      bits = w[block];
    }
  }
};
static int k, d;
static bool strong;
static std::vector<int> value, primes, anchors;
static int pair_gcd[256][256];
static Bits adjacent[256], triple_ok[256][256], ge[256], anchor_bits;
static std::vector<int> prefix;
static std::vector<unsigned long long> nodes;
static unsigned long long triples = 0, prefix_bad = 0, subset_bad = 0;
static unsigned long long support_cut = 0, large_cut = 0, anchor_cut = 0;
static std::set<std::vector<int>> survivors;

static int lcm_int(int a, int b) { return (a / std::gcd(a, b)) * b; }

static bool density_bad(const std::vector<int>& xs, int modulus) {
  int sum = 0;
  for (int x : xs) {
    sum += modulus / std::gcd(value[x], modulus);
    if (sum > modulus) return true;
  }
  return false;
}

static bool bad_subset_of_size(int size, int next, int m,
                               std::vector<int>& sub) {
  if ((int)sub.size() == size) return density_bad(sub, m);
  const int need = size - (int)sub.size();
  for (int i = next; i <= (int)prefix.size() - need; ++i) {
    int mm = m;
    for (int j : sub) mm = lcm_int(mm, pair_gcd[j][prefix[i]]);
    sub.push_back(prefix[i]);
    if (bad_subset_of_size(size, i + 1, mm, sub)) return true;
    sub.pop_back();
  }
  return false;
}

static bool any_bad_subset() {
  std::vector<int> sub;
  for (int size = 3; size <= k; ++size)
    if (bad_subset_of_size(size, 0, 1, sub)) return true;
  return false;
}

static bool eligible_final() {
  int anchor_count = 0;
  for (int i : prefix) anchor_count += value[i] % (k - 1) == 0;
  if (anchor_count == 3) {
    int outside = 0;
    for (int i : prefix)
      outside += value[i] % (k - 1) != 0 && value[i] % (k - 2) == 0;
    if (outside < 2) return false;
  }
  for (int p : primes) {
    for (int i : prefix) {
      if (value[i] % p) continue;
      int q = p;
      while (value[i] % (q * p) == 0) q *= p;
      int count = 0;
      for (int j : prefix) count += value[j] % q == 0;
      if (count < 2) return false;
    }
    if (2 * p >= k) {
      int count = 0;
      for (int i : prefix) count += value[i] % p == 0;
      if (count != 0 && count != 2) return false;
    }
  }
  return true;
}

static bool future_multiple(Bits pool, int q) {
  for (int i = pool.next(0); i < d; i = pool.next(i + 1))
    if (value[i] % q == 0) return true;
  return false;
}

static bool early_impossible(Bits pool) {
  if (!strong) return false;
  for (int p : primes) {
    std::set<int> powers;
    for (int i : prefix) {
      if (value[i] % p) continue;
      int q = p;
      while (value[i] % (q * p) == 0) q *= p;
      powers.insert(q);
    }
    for (int q : powers) {
      int count = 0;
      for (int i : prefix) count += value[i] % q == 0;
      if (count == 1 && !future_multiple(pool, q)) {
        ++support_cut;
        return true;
      }
    }
    if (2 * p >= k) {
      int count = 0;
      for (int i : prefix) count += value[i] % p == 0;
      if (count > 2 || (count == 1 && !future_multiple(pool, p))) {
        ++large_cut;
        return true;
      }
    }
  }
  int anchor_count = 0, outside = 0;
  for (int i : prefix) {
    bool anchor = value[i] % (k - 1) == 0;
    anchor_count += anchor;
    outside += !anchor && value[i] % (k - 2) == 0;
  }
  if (anchor_count == 3 && (pool & anchor_bits).none() && outside < 2 &&
      !future_multiple(pool, k - 2)) {
    ++anchor_cut;
    return true;
  }
  return false;
}

static void grow(int m, Bits pool) {
  ++nodes[prefix.size()];
  if (early_impossible(pool)) return;
  if ((int)prefix.size() == k) {
    // Necessary complete-tuple conditions are identical in both modes.
    // Apply cheap conditions before exhaustive subset-density checks.
    if (!eligible_final()) return;
    if (any_bad_subset()) {
      ++subset_bad;
      return;
    }
    std::vector<int> xs;
    for (int i : prefix) xs.push_back(value[i]);
    std::sort(xs.begin(), xs.end());
    survivors.insert(xs);
    return;
  }
  for (int x = pool.next(0); x < d; x = pool.next(x + 1)) {
    int mm = m;
    for (int y : prefix) mm = lcm_int(mm, pair_gcd[x][y]);
    prefix.push_back(x);
    if (density_bad(prefix, mm)) {
      ++prefix_bad;
      prefix.pop_back();
      continue;
    }
    Bits next = pool & adjacent[x] & ge[x];
    for (size_t t = 0; t + 1 < prefix.size(); ++t)
      next &= triple_ok[prefix[t]][x];
    grow(mm, next);
    prefix.pop_back();
  }
}

static void initialize() {
  for (int p = 2; p < k; ++p) {
    bool prime = true;
    for (int q = 2; q * q <= p; ++q) if (p % q == 0) prime = false;
    if (prime) primes.push_back(p);
  }
  std::vector<int> numbers{1};
  for (int p : primes) {
    int q = p;
    while (q * p < k) q *= p;
    std::vector<int> next;
    for (int n : numbers)
      for (int power = 1; power <= q; power *= p)
        next.push_back(n * power);
    numbers.swap(next);
  }
  for (int n : numbers) {
    int distinct = 0;
    for (int p : primes) distinct += n % p == 0;
    if (distinct >= 2) value.push_back(n);
  }
  std::sort(value.begin(), value.end());
  d = (int)value.size();
  if (d > 256) throw std::runtime_error("domain exceeds bitset capacity");
  for (int i = 0; i < d; ++i) {
    if (value[i] % (k - 1) == 0) {
      anchors.push_back(i);
      anchor_bits.set(i);
    }
    for (int j = 0; j < d; ++j) {
      int g = std::gcd(value[i], value[j]);
      pair_gcd[i][j] = g;
      if (1 < g && g < k) adjacent[i].set(j);
      if (j >= i) ge[i].set(j);
    }
  }
  for (int i = 0; i < d; ++i)
    for (int j = 0; j < d; ++j) {
      if (!adjacent[i].test(j)) continue;
      for (int x = 0; x < d; ++x) {
        if (!adjacent[i].test(x) || !adjacent[j].test(x)) continue;
        int m = lcm_int(lcm_int(pair_gcd[i][j], pair_gcd[i][x]), pair_gcd[j][x]);
        int sum = m / std::gcd(value[i], m) + m / std::gcd(value[j], m) +
                  m / std::gcd(value[x], m);
        if (sum <= m) triple_ok[i][j].set(x);
      }
    }
  nodes.resize(k + 1);
}

int main(int argc, char** argv) {
  if (argc != 3) {
    std::cerr << "usage: rule_ablation <15|16> <on|off>\n";
    return 2;
  }
  k = std::stoi(argv[1]);
  if (k != 15 && k != 16) return 2;
  strong = std::string(argv[2]) == "on";
  if (!strong && std::string(argv[2]) != "off") return 2;
  auto started = std::chrono::steady_clock::now();
  initialize();
  for (int ai = 0; ai < (int)anchors.size(); ++ai)
    for (int bi = ai; bi < (int)anchors.size(); ++bi)
      for (int ci = bi; ci < (int)anchors.size(); ++ci) {
        ++triples;
        int a = anchors[ai], b = anchors[bi], c = anchors[ci];
        if (!adjacent[a].test(b) || !adjacent[a].test(c) ||
            !adjacent[b].test(c)) continue;
        int m = lcm_int(lcm_int(pair_gcd[a][b], pair_gcd[a][c]), pair_gcd[b][c]);
        prefix = {a, b, c};
        if (density_bad(prefix, m)) continue;
        Bits pool;
        for (int x = 0; x < d; ++x) {
          if (anchor_bits.test(x) && x < c) continue;
          if (!adjacent[a].test(x) || !adjacent[b].test(x) ||
              !adjacent[c].test(x)) continue;
          if (triple_ok[a][b].test(x) && triple_ok[a][c].test(x) &&
              triple_ok[b][c].test(x)) pool.set(x);
        }
        grow(m, pool);
      }
  auto seconds = std::chrono::duration<double>(
      std::chrono::steady_clock::now() - started).count();
  std::cout << "{\"k\":" << k << ",\"strong\":"
            << (strong ? "true" : "false") << ",\"domain_size\":" << d
            << ",\"anchor_count\":" << anchors.size() << ",\"seconds\":"
            << seconds << ",\"anchor_triples\":" << triples
            << ",\"nodes_by_depth\":[";
  for (int i = 0; i <= k; ++i) {
    if (i) std::cout << ',';
    std::cout << nodes[i];
  }
  std::cout << "],\"prefix_density_reject\":" << prefix_bad
            << ",\"subset_density_reject\":" << subset_bad
            << ",\"support_cut\":" << support_cut
            << ",\"large_cut\":" << large_cut
            << ",\"anchor_cut\":" << anchor_cut
            << ",\"survivors\":[";
  bool first = true;
  for (const auto& xs : survivors) {
    if (!first) std::cout << ',';
    first = false;
    std::cout << '[';
    for (int i = 0; i < (int)xs.size(); ++i) {
      if (i) std::cout << ',';
      std::cout << xs[i];
    }
    std::cout << ']';
  }
  std::cout << "]}\n";
}
