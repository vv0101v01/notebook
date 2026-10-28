///| snc —— 非交換結構的超化／譜化：非交叉分割格 NC(n) 的 Möbius「超維數」、
///| 自由累積量 ⟷ 矩（自由機率）、von Szily 超卡特蘭數的交錯和（ℤ₂ 分次計數）、
///| 三角剖分 flip 圖的譜與直徑。
///|
///|  * `[S-D-NCPart]` |NC(n)| = Catalan(n)，n ≤ 7（枚舉 + 非交叉過濾）；
///|  * `[S-T-MobiusNC]` Kreweras：μ(0̂, π) = ∏_{B∈π} (−1)^{|B|−1}C_{|B|−1}
///|    （對 NC(6) 的每一個 π 逐一驗證——Möbius 函數即格的「超維數」，
///|    鏈上的交錯和＝ℤ₂ 分次 Euler 特徵）；
///|  * `[S-D-FreeCum]` m_n = Σ_{π∈NC(n)} ∏_{B∈π} r_{|B|}：
///|    r ≡ 1 ⟹ Marchenko–Pastur（秩 1）m_n = Cat(n)；
///|    r = e₂ ⟹ 半圓律 m_{2k} = C_k、m_奇 = 0；
///|  * `[S-D-vonSzily]` 超卡特蘭 S(m,n) = (2m)!(2n)!/(m!n!(m+n)!)
///|    = Σ_k (−1)^k C(2m, m+k)C(2n, n−k)（von Szily 交錯和，m,n ≤ 6）；
///|  * `[S-D-FlipSpec]` flip 圖譜：五邊形 flip 圖 ≅ C₅（特徵多項式相等）、
///|    N 邊形 flip 圖 = (N−3)-正則、Catalan(N−2) 個頂點、直徑 1,2,4,5,7（N=4..8）。

///| 枚舉 {0..n−1} 的所有規範化分割（塊標籤限制：前 i 個元素最多用到
///| 已出現標籤 + 1）。
pub fn all_partitions(n : Int) -> Array[Array[Int]] {
  let out : Array[Array[Int]] = []
  fn go(prefix : Array[Int], i : Int) -> Unit {
    if i == n {
      let cp : Array[Int] = []
      for x in prefix {
        let _ = cp.push(x)
      }
      let _ = out.push(cp)
      return
    }
    let maxlab = if prefix.length() == 0 { -1 } else { max_of(prefix) }
    for lab = 0; lab <= maxlab + 1; lab = lab + 1 {
      let _ = prefix.push(lab)
      go(prefix, i + 1)
      let _ = prefix.pop()
    }
  }
  go([], 0)
  out
}

fn max_of(a : Array[Int]) -> Int {
  let mut m = a[0]
  for x in a {
    if x > m {
      m = x
    }
  }
  m
}

///| 非交叉判定：不存在 a < b < c < d（循環序）使 a,c 同塊、b,d 同（另一）塊。
pub fn is_noncrossing(blocks : Array[Int]) -> Bool {
  let n = blocks.length()
  for a = 0; a < n; a = a + 1 {
    for b = a + 1; b < n; b = b + 1 {
      for c = b + 1; c < n; c = c + 1 {
        for d = c + 1; d < n; d = d + 1 {
          if blocks[a] == blocks[c] && blocks[b] == blocks[d] && blocks[a] != blocks[b] {
            return false
          }
        }
      }
    }
  }
  true
}

///| NC(n) 的全部元素（規範化塊標籤）。
pub fn nc_partitions(n : Int) -> Array[Array[Int]] {
  let out : Array[Array[Int]] = []
  for part in all_partitions(n) {
    if is_noncrossing(part) {
      let _ = out.push(part)
    }
  }
  out
}

///| 加細序：pi ≤ sigma（pi 的每塊都含於 sigma 的某塊）。
pub fn refines(pi : Array[Int], sigma : Array[Int]) -> Bool {
  let n = pi.length()
  for i = 0; i < n; i = i + 1 {
    for j = i + 1; j < n; j = j + 1 {
      if pi[i] == pi[j] && sigma[i] != sigma[j] {
        return false
      }
    }
  }
  true
}

///| 塊列表：blocks → 排序後的塊（各塊為升冪索引數組）。
pub fn block_list(blocks : Array[Int]) -> Array[Array[Int]] {
  let m : Map[Int, Array[Int]] = Map([])
  let order : Array[Int] = []
  for i = 0; i < blocks.length(); i = i + 1 {
    let b = m.get(blocks[i])
    if b is Some(arr) {
      let _ = arr.push(i)
    } else {
      m[blocks[i]] = [i]
      let _ = order.push(blocks[i])
    }
  }
  let out : Array[Array[Int]] = []
  for id in order {
    let _ = out.push(m[id])
  }
  out
}

///| Möbius 函數 μ(0̂, π)（0̂ = 全單點）：DP 遞迴
///| μ(0̂,π) = −Σ_{0̂ ≤ z < π} μ(0̂,z)。
pub fn mobius_from_bottom(n : Int) -> Map[Int, Int] {
  let ncs = nc_partitions(n)
  let bottom : Array[Int] = []
  for i = 0; i < n; i = i + 1 {
    let _ = bottom.push(i)
  }
  // 以規範化字串為鍵
  let key = fn(b : Array[Int]) -> Int {
    let mut k = 0
    for x in b {
      k = k * 10 + x + 1
    }
    k
  }
  let mu : Map[Int, Int] = Map([])
  // 先按塊數排序（塊多 = 低）
  let with_k : Array[(Int, Array[Int])] = []
  for part in ncs {
    let _ = with_k.push((block_list(part).length(), part))
  }
  let sorted = sort_by_blocks(with_k)
  // 離散分割（塊數 = n）是 0̂：μ = 1
  for pair in sorted {
    let (k, part) = pair
    let mut acc = 0
    if k == n {
      acc = 1
    } else {
      for pair2 in sorted {
        let (k2, z) = pair2
        if k2 > k && refines(z, part) {
          let mz = mu.get(key(z))
          if mz is Some(v) {
            acc = acc + v
          }
        }
      }
      acc = -acc
    }
    mu[key(part)] = acc
  }
  mu
}

fn sort_by_blocks(arr : Array[(Int, Array[Int])]) -> Array[(Int, Array[Int])] {
  let out : Array[(Int, Array[Int])] = []
  for x in arr {
    let _ = out.push(x)
  }
  // 插入排序（按塊數降冪）
  for i = 1; i < out.length(); i = i + 1 {
    let mut j = i
    while j > 0 && out[j - 1].0 < out[j].0 {
      let t = out[j - 1]
      out[j - 1] = out[j]
      out[j] = t
      j = j - 1
    }
  }
  out
}

// ------------------------------------------------------------- 自由機率 --
///| m_n = Σ_{π∈NC(n)} ∏_{B∈π} r_{|B|}（r 的索引 1..n；r[0] 不用）。
pub fn moment_from_free_cumulants(r : Array[Int], n : Int, p : Int) -> Int {
  let ncs = nc_partitions(n)
  let mut total = 0
  for part in ncs {
    let mut prod = 1
    for block in block_list(part) {
      let sz = block.length()
      prod = prod * (r[sz] % p) % p
    }
    total = (total + prod) % p
  }
  total
}

// ------------------------------------------------------------- 超卡特蘭 --
///| von Szily 交錯和（mod p）：Σ_k (−1)^k C(2m, m+k)·C(2n, n−k)。
pub fn von_szily_sum(m : Int, n : Int, p : Int) -> Int {
  let mut total = 0
  // k 的範圍：m+k ∈ [0,2m] 且 n−k ∈ [0,2n] ⟹ k ∈ [−n, m]
  for k = -n; k <= m; k = k + 1 {
    let c1 = binom_int(2 * m, m + k)
    let c2 = binom_int(2 * n, n - k)
    if c1 > 0 && c2 > 0 {
      let term = c1 % p * (c2 % p) % p
      if k % 2 != 0 {
        total = (total - term) % p
      } else {
        total = (total + term) % p
      }
    }
  }
  ((total % p) + p) % p
}

///| 超卡特蘭閉式（精確 Int64，再 mod p）：(2m)!(2n)!/(m!n!(m+n)!)。
pub fn super_catalan(m : Int, n : Int, p : Int) -> Int {
  let num = fact64(2 * m) * fact64(2 * n) / (fact64(m) * fact64(n) * fact64(m + n))
  let r = num % p.to_int64()
  ((r + p.to_int64()) % p.to_int64()).to_int()
}

fn fact64(k : Int) -> Int64 {
  let mut acc : Int64 = 1
  for i = 2; i <= k; i = i + 1 {
    acc = acc * i.to_int64()
  }
  acc
}

fn binom_int(n : Int, k : Int) -> Int {
  if k < 0 || k > n {
    return 0
  }
  let mut c : Int64 = 1
  for i = 0; i < k; i = i + 1 {
    c = c * (n - i).to_int64() / (i + 1).to_int64()
  }
  c.to_int()
}

// ------------------------------------------------------------- flip 圖 --
///| 凸 N 邊形的對角線列表（無序對 (i,j)，i<j，非邊）。
pub fn diagonals(n : Int) -> Array[(Int, Int)] {
  let out : Array[(Int, Int)] = []
  for i = 0; i < n; i = i + 1 {
    for j = i + 2; j < n; j = j + 1 {
      if !(i == 0 && j == n - 1) {
        let _ = out.push((i, j))
      }
    }
  }
  out
}

///| 兩對角線是否交叉（內部相交）。
pub fn diag_cross(d1 : (Int, Int), d2 : (Int, Int)) -> Bool {
  let (a, b) = d1
  let (c, d) = d2
  if a == c || a == d || b == c || b == d {
    return false
  }
  (a < c && c < b && b < d) || (c < a && a < d && d < b)
}

///| 枚舉三角剖分：大小 N−3 的兩兩不交叉對角線子集。
///| （N−3 條互不交叉對角線把多邊形分成 N−2 個區域；
///|  邊數和 = N + 2(N−3) = 3(N−2) ⟹ 每個區域都是三角形。）
pub fn triangulations(n : Int) -> Array[Array[Int]] {
  let diags = diagonals(n)
  let d = diags.length()
  let k = n - 3
  let out : Array[Array[Int]] = []
  let cur : Array[Int] = []
  fn go(start : Int) -> Unit {
    if cur.length() == k {
      // 檢查兩兩不交叉
      let mut ok = true
      for x = 0; x < k; x = x + 1 {
        for y = x + 1; y < k; y = y + 1 {
          if diag_cross(diags[cur[x]], diags[cur[y]]) {
            ok = false
          }
        }
      }
      if ok {
        let cp : Array[Int] = []
        for x in cur {
          let _ = cp.push(x)
        }
        let _ = out.push(cp)
      }
      return
    }
    for i = start; i < d; i = i + 1 {
      let _ = cur.push(i)
      go(i + 1)
      let _ = cur.pop()
    }
  }
  go(0)
  out
}

///| flip 鄰接：兩三角剖分恰差一條對角線。
pub fn flip_adjacent(t1 : Array[Int], t2 : Array[Int]) -> Bool {
  let mut diff = 0
  for x in t1 {
    if !contains_int(t2, x) {
      diff = diff + 1
    }
  }
  diff == 1
}

fn contains_int(a : Array[Int], x : Int) -> Bool {
  for y in a {
    if y == x {
      return true
    }
  }
  false
}

///| flip 圖鄰接矩陣（0/1，mod p），回傳 (頂點數, 矩陣)。
pub fn flip_graph(n : Int, p : Int) -> (Int, @core.Mat) {
  let ts = triangulations(n)
  let v = ts.length()
  let adj = @core.mat_build(v, v, (i, j) => {
    if i != j && flip_adjacent(ts[i], ts[j]) {
      1 % p
    } else {
      0 % p
    }
  })
  (v, adj)
}

///| BFS 直徑。
pub fn graph_diameter(v : Int, adj : @core.Mat) -> Int {
  let mut diam = 0
  for s = 0; s < v; s = s + 1 {
    let dist : Array[Int] = Array::make(v, -1)
    dist[s] = 0
    let queue : Array[Int] = [s]
    let mut head = 0
    while head < queue.length() {
      let u = queue[head]
      head = head + 1
      for w = 0; w < v; w = w + 1 {
        if adj.data[u * v + w] != 0 && dist[w] == -1 {
          dist[w] = dist[u] + 1
          let _ = queue.push(w)
        }
      }
    }
    for t = 0; t < v; t = t + 1 {
      if dist[t] > diam {
        diam = dist[t]
      }
    }
  }
  diam
}

///| 循環圖 C_n 的鄰接矩陣（mod p）。
pub fn cycle_adj(n : Int, p : Int) -> @core.Mat {
  @core.mat_build(n, n, (i, j) => {
    if (j == (i + 1) % n || j == (i + n - 1) % n) && n > 2 {
      1 % p
    } else {
      0
    }
  })
}

///| 卡特蘭數 C_k（精確 Int）。
pub fn catalan(k : Int) -> Int {
  binom_int(2 * k, k) / (k + 1)
}
