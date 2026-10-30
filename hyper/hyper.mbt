// hyper：全專案結構體的「超化」層
//
// [D-Hyper] 超運算 ⋆ : S × S → P(S) \ {∅}；超結構以完整的 (|S|² × |S|) 布林表表示。
// [Ax-HG] 規範超群（canonical hypergroup）公理：
//   (H1) 封閉性：a ⋆ b ≠ ∅
//   (H2) 結合律：(a ⋆ b) ⋆ c = a ⋆ (b ⋆ c)（以集合并展開）
//   (H3) 複製性：∪_b a ⋆ b = S
//   (H4) 交換律：a ⋆ b = b ⋆ a
//   (H5) 單位：e ⋆ a = {a}
//   (H6) 逆元：∀a ∃b 使 e ∈ a ⋆ b
// 只滿足 (H1)(H2) 者稱超半群；本檔用同一個驗證器對不同結構逐條判定。

///|
/// [D-Hyper] 有限超結構：`table[a * size + b][c]` 為真 ⟺ c ∈ a ⋆ b。
pub struct Hyper {
  size : Int32
  table : Array[Array[Bool]]
}

///|
/// [D-HyperFrom] 由判定函式 `mem(a, b, c)` 建構超結構。
pub fn hyper_from(n : Int32, mem : (Int32, Int32, Int32) -> Bool) -> Hyper {
  let table : Array[Array[Bool]] = []
  for a = 0; a < n; a = a + 1 {
    for b = 0; b < n; b = b + 1 {
      let cell : Array[Bool] = Array::make(n, false)
      for c = 0; c < n; c = c + 1 {
        cell[c] = mem(a, b, c)
      }
      table.push(cell)
    }
  }
  Hyper::{ size: n, table, }
}

///|
pub fn hyper_size(h : Hyper) -> Int32 {
  h.size
}

///|
pub fn hyper_contains(h : Hyper, a : Int32, b : Int32, c : Int32) -> Bool {
  h.table[a * h.size + b][c]
}

///|
/// [D-Cell] 單元格的基數 |a ⋆ b|。
pub fn hyper_cell_size(h : Hyper, a : Int32, b : Int32) -> Int32 {
  let cell = h.table[a * h.size + b]
  let mut s = 0
  for x in cell {
    if x {
      s = s + 1
    }
  }
  s
}

///|
/// (H1) 封閉性：每個單元格非空。
pub fn check_closure(h : Hyper) -> Bool {
  let mut ok = true
  for a = 0; a < h.size; a = a + 1 {
    for b = 0; b < h.size; b = b + 1 {
      if hyper_cell_size(h, a, b) == 0 {
        ok = false
      }
    }
  }
  ok
}

///|
/// (H4) 交換律。
pub fn check_comm(h : Hyper) -> Bool {
  let mut ok = true
  for a = 0; a < h.size; a = a + 1 {
    for b = 0; b < h.size; b = b + 1 {
      if h.table[a * h.size + b] != h.table[b * h.size + a] {
        ok = false
      }
    }
  }
  ok
}

///|
/// (H2) 結合律的左展開：{x : ∃ y ∈ b ⋆ c, x ∈ a ⋆ y}。
pub fn triple_left(h : Hyper, a : Int32, b : Int32, c : Int32) -> Array[Bool] {
  let out : Array[Bool] = Array::make(h.size, false)
  let bc = h.table[b * h.size + c]
  for y = 0; y < h.size; y = y + 1 {
    if bc[y] {
      let ay = h.table[a * h.size + y]
      for x = 0; x < h.size; x = x + 1 {
        if ay[x] {
          out[x] = true
        }
      }
    }
  }
  out
}

///|
/// (H2) 結合律的右展開：{x : ∃ y ∈ a ⋆ b, x ∈ y ⋆ c}。
pub fn triple_right(h : Hyper, a : Int32, b : Int32, c : Int32) -> Array[Bool] {
  let out : Array[Bool] = Array::make(h.size, false)
  let ab = h.table[a * h.size + b]
  for y = 0; y < h.size; y = y + 1 {
    if ab[y] {
      let yc = h.table[y * h.size + c]
      for x = 0; x < h.size; x = x + 1 {
        if yc[x] {
          out[x] = true
        }
      }
    }
  }
  out
}

///|
pub fn check_assoc(h : Hyper) -> Bool {
  let mut ok = true
  for a = 0; a < h.size; a = a + 1 {
    for b = 0; b < h.size; b = b + 1 {
      for c = 0; c < h.size; c = c + 1 {
        if triple_left(h, a, b, c) != triple_right(h, a, b, c) {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// (H3) 複製性：對每個 a，∪_b (a ⋆ b) = S。
pub fn check_repro(h : Hyper) -> Bool {
  let mut ok = true
  for a = 0; a < h.size; a = a + 1 {
    let acc : Array[Bool] = Array::make(h.size, false)
    for b = 0; b < h.size; b = b + 1 {
      let cell = h.table[a * h.size + b]
      for c = 0; c < h.size; c = c + 1 {
        if cell[c] {
          acc[c] = true
        }
      }
    }
    for c = 0; c < h.size; c = c + 1 {
      if !acc[c] {
        ok = false
      }
    }
  }
  ok
}

///|
/// (H5) 單位元：e ⋆ a = a ⋆ e = {a}。
pub fn check_identity(h : Hyper, e : Int32) -> Bool {
  let mut ok = true
  for a = 0; a < h.size; a = a + 1 {
    if hyper_cell_size(h, e, a) != 1 || !hyper_contains(h, e, a, a) {
      ok = false
    }
    if hyper_cell_size(h, a, e) != 1 || !hyper_contains(h, a, e, a) {
      ok = false
    }
  }
  ok
}

///|
/// (H6) 逆元存在：∀a ∃b 使 e ∈ a ⋆ b。
pub fn check_inverse(h : Hyper, e : Int32) -> Bool {
  let mut ok = true
  for a = 0; a < h.size; a = a + 1 {
    let mut found = false
    for b = 0; b < h.size; b = b + 1 {
      if hyper_contains(h, a, b, e) {
        found = true
      }
    }
    if !found {
      ok = false
    }
  }
  ok
}

///|
/// [E-HyperClassify] 六條公理的判定向量 → 結構分類。
///   回傳 (閉, 結合, 複製, 交換, 單位, 逆元)。
pub fn hyper_classify(
  h : Hyper,
  e : Int32,
) -> (Bool, Bool, Bool, Bool, Bool, Bool) {
  (
    check_closure(h),
    check_assoc(h),
    check_repro(h),
    check_comm(h),
    check_identity(h, e),
    check_inverse(h, e),
  )
}

///|
pub fn is_canonical_hypergroup(h : Hyper, e : Int32) -> Bool {
  let (c, a, r, m, i, inv) = hyper_classify(h, e)
  c && a && r && m && i && inv
}

///|
/// [D-HyperPow] k 重超積：以 a 反覆自乘的**集合**（{a}, a⋆a, (a⋆a)⋆a, …）之并。
pub fn hyper_pow(h : Hyper, a : Int32, k : Int32) -> Array[Bool] {
  let acc : Array[Bool] = Array::make(h.size, false)
  acc[a] = true
  // 逐步以「整塊相乘」推進：acc ← acc ⋆ acc
  for _step = 0; _step < k; _step = _step + 1 {
    let next : Array[Bool] = Array::make(h.size, false)
    for x = 0; x < h.size; x = x + 1 {
      if acc[x] {
        for y = 0; y < h.size; y = y + 1 {
          if acc[y] {
            let cell = h.table[x * h.size + y]
            for z = 0; z < h.size; z = z + 1 {
              if cell[z] {
                next[z] = true
              }
            }
          }
        }
      }
    }
    for z = 0; z < h.size; z = z + 1 {
      if next[z] {
        acc[z] = true
      }
    }
  }
  acc
}

///|
/// [E-Potency] 超結構在元素 a 上的**冪零度**：最小的 k 使 a^(*k) = a^(*k+1)（集合穩定）。
///   未在 `cap` 步內穩定則回傳 −1。這是把「代數次數」提升到集合層的算法。
pub fn hyper_potency(h : Hyper, a : Int32, cap : Int32) -> Int32 {
  let mut prev = hyper_pow(h, a, 0)
  let mut k = 1
  while k <= cap {
    let cur = hyper_pow(h, a, k)
    if cur == prev {
      return k
    }
    prev = cur
    k = k + 1
  }
  -1
}

// ---------------------------------------------------------------------------
// 具體超結構：對專案中的每個結構各做一次超化
// ---------------------------------------------------------------------------

///|
/// [D-Hyper-Interval] 全序集上的「區間超化」：a ⋆ b = {c : min(a,b) ≤ c ≤ max(a,b)}。
///   這是把**序結構**超化的標準方式。
pub fn interval_hyper(n : Int32) -> Hyper {
  hyper_from(n, (a, b, c) => {
    let lo = if a < b { a } else { b }
    let hi = if a < b { b } else { a }
    c >= lo && c <= hi
  })
}

///|
/// [D-Hyper-Trunc] 秩的「截斷加法超化」：a ⊛ b = {c : c ≤ min(r, a + b)}。
///   這是 [P-Subadd]（rank(A+B) ≤ rank A + rank B）的**超結構形式**：
///   定理「秩次可加」等價於「秩集合對 ⊛ 封閉」。
pub fn truncated_add_hyper(r : Int32) -> Hyper {
  hyper_from(r + 1, (a, b, c) => {
    let cap = if a + b < r { a + b } else { r }
    c <= cap
  })
}

///|
/// [D-Hyper-Geodesic] 一般有限度量圖上的「測地區間超化」：
///   a ⋆ b = {c : d(a,c) + d(c,b) = d(a,b)}（a 到 b 的最短路徑上的點）。
///   `dist` 為 n×n 距離矩陣；不可達以 −1 表示。
pub fn geodesic_hyper(dist : Array[Array[Int32]], n : Int32) -> Hyper {
  hyper_from(n, (a, b, c) => {
    let d = dist[a][b]
    if d < 0 {
      false
    } else {
      dist[a][c] >= 0 && dist[c][b] >= 0 && dist[a][c] + dist[c][b] == d
    }
  })
}

///|
/// [D-Hyper-Metric] 由度量空間（@metric.MSpace）超化：取 d = 整數距離。
pub fn metric_hyper(m : @metric.MSpace) -> Hyper {
  let n = m.n
  let dist : Array[Array[Int32]] = Array::makei(n, i => {
    Array::makei(n, j => @metric.mspace_get(m, i, j))
  })
  geodesic_hyper(dist, n)
}

///|
/// [D-Hyper-TensorRank] 張量秩的超化：載體 {0,1,2,3}（3 = 「≥3」），
///   a ⊛ b = {c : c ≤ min(3, a + b)}。F₃ 上 6561 個張量的秩分佈使這一層是**飽和**的。
pub fn tensor_rank_hyper() -> Hyper {
  truncated_add_hyper(3)
}

///|
/// [D-Hyper-MatRank] 矩陣秩的超化（載體 {0..n}）：由 F_p 上**實際的**秩資料建構 ——
///   對每一對秩 (r,s)，收集所有能由 A+B（rank A = r, rank B = s）達到的秩。
///   n = 2 時窮舉全部矩陣對；回傳 (超結構, 到位判定)。
pub fn mat_rank_hyper_exhaustive(n : Int32, p : Int32) -> (Hyper, Bool) {
  let total = @core.int_pow(p, n * n)
  let mats : Array[@core.Mat] = []
  let ranks : Array[Int32] = []
  let f = @core.mk_field(p)
  for code = 0; code < total; code = code + 1 {
    let mut c = code
    let m = @core.mat_make(n, n, 0)
    for i = 0; i < n * n; i = i + 1 {
      m.data[i] = c % p
      c = c / p
    }
    mats.push(m)
    ranks.push(@core.rank_mod(m, f))
  }
  let table : Array[Array[Bool]] = []
  for r = 0; r <= n; r = r + 1 {
    for s = 0; s <= n; s = s + 1 {
      let cell : Array[Bool] = Array::make(n + 1, false)
      for i = 0; i < mats.length(); i = i + 1 {
        if ranks[i] == r {
          for j = 0; j < mats.length(); j = j + 1 {
            if ranks[j] == s {
              let sm = @core.mat_add(mats[i], mats[j], p)
              cell[@core.rank_mod(sm, f)] = true
            }
          }
        }
      }
      table.push(cell)
    }
  }
  // 到位性：對每個 (r,s)，區間 [|r−s|, min(n,r+s)] 內的每個 t 都出現
  let mut ok = true
  for r = 0; r <= n; r = r + 1 {
    for s = 0; s <= n; s = s + 1 {
      let lo = if r > s { r - s } else { s - r }
      let hi0 = r + s
      let hi = if hi0 < n { hi0 } else { n }
      for t = lo; t <= hi; t = t + 1 {
        if !table[r * (n + 1) + s][t] {
          ok = false
        }
      }
    }
  }
  (Hyper::{ size: n + 1, table, }, ok)
}

///|
/// [D-Hyper-Flip] 翻轉圖（associahedron 的 1-骨架）上的測地超化。
///   先以 BFS 由 `@nc.triangulations(n)` 建出翻轉圖距離。
pub fn flip_hyper(n : Int32) -> Hyper {
  let tris = @nc.triangulations(n)
  let k = tris.length()
  let inf = 1000000
  let dist : Array[Array[Int32]] = Array::makei(k, _ => Array::make(k, inf))
  for i = 0; i < k; i = i + 1 {
    dist[i][i] = 0
    for j = 0; j < k; j = j + 1 {
      if i != j && @nc.are_flippable(tris[i], tris[j]) {
        dist[i][j] = 1
      }
    }
  }
  // Floyd–Warshall
  for m = 0; m < k; m = m + 1 {
    for i = 0; i < k; i = i + 1 {
      for j = 0; j < k; j = j + 1 {
        let via = dist[i][m] + dist[m][j]
        if via < dist[i][j] {
          dist[i][j] = via
        }
      }
    }
  }
  geodesic_hyper(dist, k)
}

///|
pub fn hyper_cell_profile(h : Hyper) -> Array[Int32] {
  let prof : Array[Int32] = Array::make(h.size + 1, 0)
  for a = 0; a < h.size; a = a + 1 {
    for b = 0; b < h.size; b = b + 1 {
      let s = hyper_cell_size(h, a, b)
      if s <= h.size {
        prof[s] = prof[s] + 1
      }
    }
  }
  prof
}

///|
/// [D-Hyper-AbsDiff] 「帶差的區間超化」：a ⊛ b = {c : |a−b| ≤ c ≤ min(n, a+b)}。
///   這正是矩陣秩（n×n 上）的加法律；與下方 `crisp_cyclic_hyper` 對比可知：
///   **能否作差**決定超結構是否為規範超群。
pub fn abs_diff_hyper(n : Int32) -> Hyper {
  hyper_from(n + 1, (a, b, c) => {
    let lo = if a > b { a - b } else { b - a }
    let hi0 = a + b
    let hi = if hi0 < n { hi0 } else { n }
    c >= lo && c <= hi
  })
}

///|
/// [D-Hyper-Krasner] Krasner 超域（加性）：載體 {0,1}，1 ⊛ 1 = {0,1}，其餘為單點。
///   意義：1 + 1 的結果取決於特徵，超化把這個不確定性保留下來。
pub fn krasner_hyper() -> Hyper {
  hyper_from(2, (a, b, c) => {
    if a == 0 {
      c == b
    } else if b == 0 {
      c == 1
    } else {
      true
    }
  })
}

///|
/// [D-Hyper-Crisp] 脆（crisp）超群：ℤ/n 的加法。所有單元格都是單點 ⟹ 規範超群。
///   用途：作為驗證器的陽性對照（群 = 退化的超群）。
pub fn crisp_cyclic_hyper(n : Int32) -> Hyper {
  hyper_from(n, (a, b, c) => (a + b) % n == c)
}
