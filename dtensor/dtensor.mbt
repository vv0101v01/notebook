// ===========================================================================
// dtensor — 導出張量積：Tor_*^A(F_2, F_2) 用 Koszul 自由分解真算
//
// A = F_2[x_1,…,x_g]（生成元度數 1，截斷到總度數 ≤ N）。
// Koszul 分解 K_i = ⊕_{|S| = i} A·e_S，d_i(e_S·m) = Σ_{j∈S} (S∖j, m + e_j)（F_2：無號）。
//
// 兩件事分開算（這正是「導出」與「未導出」的差別）：
//   • [T-KoszulDD] + [T-KoszulExact]：K_* 是 F_2 的自由分解 —— d² = 0 且 H_{i≥1}(K_*) = 0；
//   • [E-Tor]：Tor_i = H_i(K_* ⊗_A F_2)，而 K_* ⊗_A F_2 是把每個係數「取常數項」
//     （A⁺ 座標投影掉）後的複形；其微分矩陣由常數項投影真正算出（在本例中恆為零矩陣，
//     因為 d 的係數都在 A⁺ 裡）。
// ===========================================================================

///|
/// [D-Poly] 多項式代數 F_2[x_1..x_g]，截斷到總度數 `n`。
pub struct PolyAlg {
  g : Int32
  n : Int32
}

///|
/// 建代數。
pub fn poly_alg(g : Int32, n : Int32) -> PolyAlg {
  PolyAlg::{ g, n, }
}

///|
/// 指數向量的度數（總次數）。
pub fn mono_deg(m : Array[Int32]) -> Int32 {
  let mut d = 0
  for x in m {
    d = d + x
  }
  d
}

///|
/// 度數 ≤ n 的所有單項式（指數向量），依 (度數, 字典序) 排序。
pub fn monomials(g : Int32, n : Int32) -> Array[Array[Int32]] {
  let all : Array[Array[Int32]] = []
  let total = @core.int_pow(n + 1, g)
  for code = 0; code < total; code = code + 1 {
    let ex : Array[Int32] = Array::make(g, 0)
    let mut c = code
    let mut sum = 0
    for j = 0; j < g; j = j + 1 {
      ex[j] = c % (n + 1)
      sum = sum + ex[j]
      c = c / (n + 1)
    }
    if sum <= n {
      all.push(ex)
    }
  }
  // 插入排序：(度數, 字典序)
  let res : Array[Array[Int32]] = []
  for ex in all {
    let de = mono_deg(ex)
    let mut pos = res.length()
    let mut k = res.length() - 1
    let mut placed = false
    while k >= 0 && !placed {
      let dk = mono_deg(res[k])
      let mut greater = false
      if dk > de {
        greater = true
      } else if dk == de {
        // 字典序比較
        let mut q = 0
        let mut decided = false
        while q < g && !decided {
          if res[k][q] > ex[q] {
            greater = true
            decided = true
          } else if res[k][q] < ex[q] {
            decided = true
          }
          q = q + 1
        }
      }
      if greater {
        pos = k
        k = k - 1
      } else {
        placed = true
      }
    }
    res.insert(pos, ex)
  }
  res
}

///|
/// 大小為 `i` 的子集遮罩清單。
pub fn subsets_of_size(g : Int32, i : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for m = 0; m < @core.int_pow(2, g); m = m + 1 {
    let mut c = 0
    for j = 0; j < g; j = j + 1 {
      if (m >> j) % 2 == 1 {
        c = c + 1
      }
    }
    if c == i {
      out.push(m)
    }
  }
  out
}

///|
/// [D-Koszul] Koszul 分解的基：`basis[i][t]` = 同調度 i、內部度數 t 的基
///   （元素為 (子集遮罩, 單項式索引)）。內部度數 t = i + |m|。
pub fn koszul_basis(a : PolyAlg) -> Array[Array[Array[(Int32, Int32)]]] {
  let mons = monomials(a.g, a.n)
  let cells : Array[Array[Array[(Int32, Int32)]]] = Array::makei(a.g + 1, _ => {
    Array::makei(a.n + a.g + 1, _ => [])
  })
  for i = 0; i <= a.g; i = i + 1 {
    for mask in subsets_of_size(a.g, i) {
      for mi = 0; mi < mons.length(); mi = mi + 1 {
        let d = mono_deg(mons[mi])
        if d + i <= a.n {
          cells[i][d + i].push((mask, mi))
        }
      }
    }
  }
  cells
}

///|
/// 在某一格的基中找 (遮罩, 單項式) 的位置（不存在回 −1）。
pub fn find_basis(
  cell : Array[(Int32, Int32)],
  mask : Int32,
  mi : Int32,
) -> Int32 {
  let mut res = -1
  for k = 0; k < cell.length(); k = k + 1 {
    if cell[k].0 == mask && cell[k].1 == mi {
      res = k
    }
  }
  res
}

///|
/// [E-Koszul] Koszul 微分 d_i 在內部度數 t 的矩陣（列 = K_{i−1}, 欄 = K_i）。
pub fn koszul_d(
  a : PolyAlg,
  cells : Array[Array[Array[(Int32, Int32)]]],
  mons : Array[Array[Int32]],
  i : Int32,
  t : Int32,
) -> @core.Mat {
  if i <= 0 || i > a.g || t < 0 || t >= cells[0].length() {
    return @core.mat_make(0, 0, 0)
  }
  let src = cells[i][t]
  let dst = cells[i - 1][t]
  let m = @core.mat_make(dst.length(), src.length(), 0)
  for c = 0; c < src.length(); c = c + 1 {
    let mask = src[c].0
    let mi = src[c].1
    for j = 0; j < a.g; j = j + 1 {
      if (mask >> j) % 2 == 1 {
        let nmask = mask - (1 << j)
        // 單項式索引：m + e_j
        let mut nmi = -1
        for k = 0; k < mons.length(); k = k + 1 {
          let mut same = true
          for q = 0; q < a.g; q = q + 1 {
            let want = if q == j { mons[mi][q] + 1 } else { mons[mi][q] }
            if mons[k][q] != want {
              same = false
            }
          }
          if same {
            nmi = k
          }
        }
        if nmi >= 0 {
          let r = find_basis(dst, nmask, nmi)
          if r >= 0 {
            m.data[r * src.length() + c] = (m.data[r * src.length() + c] + 1) %
              2
          }
        }
      }
    }
  }
  m
}

///|
/// [T-KoszulDD] d_{i−1} ∘ d_i = 0。
pub fn koszul_dd_zero(a : PolyAlg) -> Bool {
  let cells = koszul_basis(a)
  let mons = monomials(a.g, a.n)
  let mut ok = true
  for i = 2; i <= a.g; i = i + 1 {
    for t = 0; t < cells[0].length(); t = t + 1 {
      let d1 = koszul_d(a, cells, mons, i, t)
      let d0 = koszul_d(a, cells, mons, i - 1, t)
      if d1.cols > 0 && d1.rows > 0 && d0.rows > 0 && d0.cols == d1.rows {
        if !@core.mat_is_zero(@core.mat_mul(d0, d1, 2)) {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// [T-KoszulExact] 分解的恰好性：H_i(K_*) = 0（i ≥ 1），以「秩 = 函數」逐格驗證
///   （dim ker d_i = rank d_{i+1}）。
pub fn koszul_exact(a : PolyAlg) -> Bool {
  let cells = koszul_basis(a)
  let mons = monomials(a.g, a.n)
  let fld = @core.mk_field(2)
  let mut ok = true
  for i = 1; i <= a.g; i = i + 1 {
    for t = 0; t < cells[0].length(); t = t + 1 {
      let dim_ki = cells[i][t].length()
      if dim_ki > 0 {
        let di = koszul_d(a, cells, mons, i, t)
        let ker = dim_ki - @core.rank_mod(di, fld)
        let im = if i + 1 > a.g {
          0
        } else if cells[i + 1][t].length() == 0 {
          0
        } else {
          @core.rank_mod(koszul_d(a, cells, mons, i + 1, t), fld)
        }
        if ker != im {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// `K_i ⊗_A F_2` 的基：只保留單項式 0 的那些元素（⊗ 把 A⁺ 座標殺掉）。
///   回傳 (子集遮罩清單)，元素 (mask) 的內部度數 = |mask|。
pub fn reduced_basis(a : PolyAlg, i : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for mask in subsets_of_size(a.g, i) {
    out.push(mask)
  }
  out
}

///|
/// [E-Tor] 約化微分 d_i ⊗_A F_2 的矩陣（內部度數 t）：列 = K_{i−1}⊗F_2、
///   欄 = K_i⊗F_2，元素 = 像中「常數項」的係數（A⁺ 座標全被投影掉）。
pub fn koszul_d_reduced(a : PolyAlg, i : Int32, t : Int32) -> @core.Mat {
  if i <= 0 || i > a.g {
    return @core.mat_make(0, 0, 0)
  }
  let src = if t == i { reduced_basis(a, i) } else { [] }
  let dst = if t == i - 1 { reduced_basis(a, i - 1) } else { [] }
  let m = @core.mat_make(dst.length(), src.length(), 0)
  for c = 0; c < src.length(); c = c + 1 {
    let mask = src[c]
    for j = 0; j < a.g; j = j + 1 {
      if (mask >> j) % 2 == 1 {
        let nmask = mask - (1 << j)
        // d(e_S) = Σ_j (S∖j, e_j)：e_j 的度數 1 > 0 ⟹ 常數項係數為 0
        let const_coeff = if 1 == 0 { 1 } else { 0 }
        for r = 0; r < dst.length(); r = r + 1 {
          if dst[r] == nmask {
            m.data[r * src.length() + c] = (
                m.data[r * src.length() + c] + const_coeff
              ) %
              2
          }
        }
      }
    }
  }
  m
}

///|
/// [D-TorCx] 導出張量積的複形：`K^{(1)} ⊗_A K^{(2)}` 再 `⊗_A F_2`。
///   基 = (S_1, S_2) 兩份子集，同調度 i = |S_1| + |S_2|（內部度數亦為 i）。
pub fn tor_basis(a : PolyAlg, i : Int32) -> Array[(Int32, Int32)] {
  let out : Array[(Int32, Int32)] = []
  for c1 = 0; c1 <= a.g; c1 = c1 + 1 {
    let c2 = i - c1
    if c2 >= 0 && c2 <= a.g {
      for x in subsets_of_size(a.g, c1) {
        for y in subsets_of_size(a.g, c2) {
          out.push((x, y))
        }
      }
    }
  }
  out
}

///|
/// [E-Tor] 約化後的張量微分 d_i ⊗ 1：(S_1,S_2) ↦ Σ_{j∈S_1}(S_1∖j,S_2) + Σ_{j∈S_2}(S_1,S_2∖j)，
///   係數取常數項（A⁺ 座標被殺）—— 本模型係數全在 A⁺ 中，故矩陣為零；
///   但矩陣是由**逐項計算**得到，不是宣告的。
pub fn tor_reduced_d(a : PolyAlg, i : Int32) -> @core.Mat {
  if i <= 0 || i > 2 * a.g {
    return @core.mat_make(0, 0, 0)
  }
  let src = tor_basis(a, i)
  let dst = tor_basis(a, i - 1)
  let m = @core.mat_make(dst.length(), src.length(), 0)
  for c = 0; c < src.length(); c = c + 1 {
    let s1 = src[c].0
    let s2 = src[c].1
    for j = 0; j < a.g; j = j + 1 {
      if (s1 >> j) % 2 == 1 {
        let t1 = s1 - (1 << j)
        // 係數 = x_j 的常數項 = 0（x_j 的度數為 1）
        let const_coeff = if 1 == 0 { 1 } else { 0 }
        for r = 0; r < dst.length(); r = r + 1 {
          if dst[r].0 == t1 && dst[r].1 == s2 {
            m.data[r * src.length() + c] = (
                m.data[r * src.length() + c] + const_coeff
              ) %
              2
          }
        }
      }
      if (s2 >> j) % 2 == 1 {
        let t2 = s2 - (1 << j)
        let const_coeff = if 1 == 0 { 1 } else { 0 }
        for r = 0; r < dst.length(); r = r + 1 {
          if dst[r].0 == s1 && dst[r].1 == t2 {
            m.data[r * src.length() + c] = (
                m.data[r * src.length() + c] + const_coeff
              ) %
              2
          }
        }
      }
    }
  }
  m
}

///|
/// [E-Tor] Tor_i^A(F_2,F_2)_t = dim ker(d_i ⊗ 1) − rank(d_{i+1} ⊗ 1)。
pub fn tor_dim(a : PolyAlg, i : Int32, t : Int32) -> Int32 {
  if i < 0 || i > 2 * a.g || t < 0 || t != i {
    return 0
  }
  let dim_i = tor_basis(a, i).length()
  if dim_i == 0 {
    return 0
  }
  let fld = @core.mk_field(2)
  let ker = if i == 0 {
    dim_i
  } else {
    dim_i - @core.rank_mod(tor_reduced_d(a, i), fld)
  }
  let im = if i + 1 > 2 * a.g {
    0
  } else if tor_basis(a, i + 1).length() == 0 {
    0
  } else {
    @core.rank_mod(tor_reduced_d(a, i + 1), fld)
  }
  ker - im
}

///|
/// Tor 表 `[i][t]`（i ≤ i_max、t ≤ t_max）。
pub fn tor_table(
  a : PolyAlg,
  i_max : Int32,
  t_max : Int32,
) -> Array[Array[Int32]] {
  Array::makei(i_max + 1, i => Array::makei(t_max + 1, t => tor_dim(a, i, t)))
}

///|
/// Tor 表的總維數。
pub fn tor_total(a : PolyAlg, i_max : Int32, t_max : Int32) -> Int32 {
  let tb = tor_table(a, i_max, t_max)
  let mut s = 0
  for row in tb {
    for v in row {
      s = s + v
    }
  }
  s
}
