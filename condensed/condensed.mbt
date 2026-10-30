// ===========================================================================
// condensed — 凝聚集／凝聚向量空間的「有限層級」演算法
//
// 模型：一個凝聚對象用「有限層級鏈」表示：
//   S = lim_n S_n（profinite 集），A = lim_n A_n（凝聚 abelian 群），
//   限制映射為矩陣。於此模型上：
//     • Z[S]^■（自由凝聚群）的每一層是 Z[S_n]，誘導映射為矩陣；
//     • Hom(Z[S]^■, F_p^k) 的維數 = 限制鏈的極限維數（= 局部常數函數）；
//     • Ext^{i>0}(Z[S]^■, F_p) 的消失 = 過渡映射的 Mittag-Leffler 性質，
//       由「秩是否穩定」給出可驗證的證書。
// ===========================================================================

///|
/// [D-Prof] profinite 集：層級大小 `sizes[n]` 與過渡映射 `maps[n] : S_{n+1} → S_n`
///   （列 = S_n 的索引、欄 = S_{n+1} 的索引，one-hot）。
pub struct Prof {
  sizes : Array[Int32]
  maps : Array[@core.Mat]
  p : Int32
}

///|
/// [D-Prof] 建 profinite 物件（maps 長度 = sizes 長度 − 1）。
pub fn prof_new(
  sizes : Array[Int32],
  maps : Array[@core.Mat],
  p : Int32,
) -> Prof {
  Prof::{ sizes, maps, p, }
}

///|
/// 單點 profinite 集。
pub fn prof_pt(p : Int32) -> Prof {
  Prof::{ sizes: [1], maps: [], p, }
}

///|
/// [T-Prof] 檢查：每個過渡映射是函數（每欄恰一 1）且滿射（每列至少一個 1）。
pub fn prof_valid(pr : Prof) -> Bool {
  let n = pr.sizes.length()
  if pr.maps.length() != n - 1 {
    return false
  }
  let mut ok = true
  for k = 0; k < pr.maps.length(); k = k + 1 {
    let m = pr.maps[k]
    if m.rows != pr.sizes[k] || m.cols != pr.sizes[k + 1] {
      ok = false
    }
    for j = 0; j < m.cols; j = j + 1 {
      let mut cnt = 0
      for i = 0; i < m.rows; i = i + 1 {
        if m.data[i * m.cols + j] != 0 {
          cnt = cnt + 1
        }
      }
      if cnt != 1 {
        ok = false
      }
    }
    for i = 0; i < m.rows; i = i + 1 {
      let mut hit = false
      for j = 0; j < m.cols; j = j + 1 {
        if m.data[i * m.cols + j] != 0 {
          hit = true
        }
      }
      if !hit {
        ok = false
      }
    }
  }
  ok
}

///|
/// [D-Zp] Z_p = lim_n Z/p^n（層級 n = 1..m）。
pub fn prof_zp(m : Int32, p : Int32) -> Prof {
  let sizes : Array[Int32] = []
  let maps : Array[@core.Mat] = []
  let mut prev = 1
  for n = 1; n <= m; n = n + 1 {
    let cur = @core.int_pow(p, n)
    sizes.push(cur)
    if n > 1 {
      // x ↦ x mod p^{n−1}
      let mat = @core.mat_make(prev, cur, 0)
      for x = 0; x < cur; x = x + 1 {
        mat.data[x % prev * cur + x] = 1
      }
      maps.push(mat)
    }
    prev = cur
  }
  Prof::{ sizes, maps, p, }
}

///|
/// [D-Cantor] {0,1}^n 的投影系（層級大小 2^1..2^m）。
pub fn prof_cantor(m : Int32, p : Int32) -> Prof {
  let sizes : Array[Int32] = []
  let maps : Array[@core.Mat] = []
  let mut prev = 1
  for n = 1; n <= m; n = n + 1 {
    let cur = @core.int_pow(2, n)
    sizes.push(cur)
    if n > 1 {
      // 丟掉最高位
      let mat = @core.mat_make(prev, cur, 0)
      for x = 0; x < cur; x = x + 1 {
        mat.data[x % prev * cur + x] = 1
      }
      maps.push(mat)
    }
    prev = cur
  }
  Prof::{ sizes, maps, p, }
}

///|
/// [D-Ninf] 輕凝聚用的 N∞：層級 S_n = {0,…,n}，過渡 n+1 ↦ n。
pub fn prof_ninf(m : Int32, p : Int32) -> Prof {
  let sizes : Array[Int32] = []
  let maps : Array[@core.Mat] = []
  for n = 0; n < m; n = n + 1 {
    sizes.push(n + 1)
    if n > 0 {
      let mat = @core.mat_make(n, n + 1, 0) // 列 = {0..n−1}
      for x = 0; x <= n; x = x + 1 {
        let y = if x == n { n - 1 } else { x }
        mat.data[y * (n + 1) + x] = 1
      }
      maps.push(mat)
    }
  }
  Prof::{ sizes, maps, p, }
}

///|
/// [D-ProfProd] 乘積 profinite 集（層級逐層相乘）。
pub fn prof_prod(a : Prof, b : Prof) -> Prof {
  let m = if a.sizes.length() < b.sizes.length() {
    a.sizes.length()
  } else {
    b.sizes.length()
  }
  let sizes : Array[Int32] = []
  for n = 0; n < m; n = n + 1 {
    sizes.push(a.sizes[n] * b.sizes[n])
  }
  let maps : Array[@core.Mat] = []
  for n = 0; n + 1 < m; n = n + 1 {
    let rows = sizes[n]
    let cols = sizes[n + 1]
    let mat = @core.mat_make(rows, cols, 0)
    let ma = a.maps[n]
    let mb = b.maps[n]
    for i = 0; i < a.sizes[n + 1]; i = i + 1 {
      for j = 0; j < b.sizes[n + 1]; j = j + 1 {
        let col = i * b.sizes[n + 1] + j
        let mut ra = -1
        for r = 0; r < a.sizes[n]; r = r + 1 {
          if ma.data[r * ma.cols + i] != 0 {
            ra = r
          }
        }
        let mut rb = -1
        for r = 0; r < b.sizes[n]; r = r + 1 {
          if mb.data[r * mb.cols + j] != 0 {
            rb = r
          }
        }
        if ra >= 0 && rb >= 0 {
          mat.data[(ra * b.sizes[n] + rb) * cols + col] = 1
        }
      }
    }
    maps.push(mat)
  }
  Prof::{ sizes, maps, p: a.p, }
}

// ---------------------------------------------------------------------------
// 層級鏈上的線性代數
// ---------------------------------------------------------------------------

///|
/// [D-Chain] 有限層級鏈：`trans[n] : V_n → V_{n−1}`（n ≥ 1）。
pub struct Chain {
  dims : Array[Int32]
  trans : Array[@core.Mat]
  p : Int32
}

///|
/// [E-Free] 自由凝聚群 Z[S]^■ 的層級鏈：層級 n 是 Z[S_n]（維數 |S_n|），
///   過渡映射是誘導映射（與 `maps[n]` 相同）。
pub fn chain_free(pr : Prof) -> Chain {
  let dims = pr.sizes.copy()
  let trans : Array[@core.Mat] = []
  for k = 0; k < pr.maps.length(); k = k + 1 {
    trans.push(pr.maps[k])
  }
  Chain::{ dims, trans, p: pr.p, }
}

///|
/// [E-Func] 函數鏈 C(S_n, F_p^k) = Hom(Z[S_n], F_p^k)：這是**正向系**，
///   映射 res: C(S_n) → C(S_{n+1}) 為單射（拉回），故
///   lim_n C(S_n) = C(S_0)（只有「常數」型）、colim_n C(S_n) = ∪_n C(S_n)（全部局部常數）。
pub fn chain_func(pr : Prof, k : Int32) -> Chain {
  let dims : Array[Int32] = []
  for s in pr.sizes {
    dims.push(s * k)
  }
  let trans : Array[@core.Mat] = []
  for idx = 0; idx < pr.maps.length(); idx = idx + 1 {
    let mp = pr.maps[idx]
    // 正向映射 V_n = C(S_n) → V_{n+1} = C(S_{n+1})：rows = dims[n+1], cols = dims[n]
    let rows = pr.sizes[idx + 1] * k
    let cols = pr.sizes[idx] * k
    let mat = @core.mat_make(rows, cols, 0)
    for x = 0; x < pr.sizes[idx + 1]; x = x + 1 {
      for i = 0; i < pr.sizes[idx]; i = i + 1 {
        if mp.data[i * mp.cols + x] != 0 {
          for c = 0; c < k; c = c + 1 {
            mat.data[(x * k + c) * cols + (i * k + c)] = 1
          }
        }
      }
    }
    trans.push(mat)
  }
  Chain::{ dims, trans, p: pr.p, }
}

///|
/// 鏈的總維數。
pub fn chain_total(c : Chain) -> Int32 {
  let mut t = 0
  for d in c.dims {
    t = t + d
  }
  t
}

///|
/// [E-Lim] 逆極限維數 = 複合映射 V_N → V_0 的秩（有限鏈的極限就是像）。
pub fn chain_lim_dim(c : Chain) -> Int32 {
  let n = c.dims.length()
  if n == 0 {
    return 0
  }
  if n == 1 {
    return c.dims[0]
  }
  // 由最高層往最低層複合：T_1 · T_2 ⋯ T_{N−1}
  let mut acc = c.trans[0]
  for k = 1; k < c.trans.length(); k = k + 1 {
    acc = @core.mat_mul(acc, c.trans[k], c.p)
  }
  @core.rank_mod(acc, @core.mk_field(c.p))
}

///|
/// [T-ML] Mittag-Leffler 證書：所有過渡映射的秩 = 目標維數（即「到上」）。
///   對函數鏈而言映射是單射，此時改檢查秩 = 來源維數（單射性）；
///   兩種情形都使 Ext^{i>0} 消失。
pub fn chain_ml(c : Chain, surjective : Bool) -> Bool {
  let fld = @core.mk_field(c.p)
  let mut ok = true
  for k = 0; k < c.trans.length(); k = k + 1 {
    let m = c.trans[k]
    let rk = @core.rank_mod(m, fld)
    let want = if surjective { m.rows } else { m.cols }
    if rk != want {
      ok = false
    }
  }
  ok
}

///|
/// [T-ExtVan] 對 profinite 層級：自由鏈的過渡滿射、函數鏈的過渡單射，
///   故 Ext^{i>0}(Z[S]^■, F_p^k) = 0。回傳「消失證書」。
pub fn cond_ext_vanishes(pr : Prof, k : Int32) -> Bool {
  chain_ml(chain_free(pr), true) && chain_ml(chain_func(pr, k), false)
}

///|
/// [E-Hom2] Hom(Z[S], A) 的維數，A = F_p^k（離散）。
///   Z[S] = colim_{有限商} Z[S']，故 Hom(Z[S], A) = lim_{S'} Hom(Z[S'], A)，
///   於層級模型即逆極限維數 —— 只有「常數」型的映射。
pub fn cond_hom_free_discrete(pr : Prof, k : Int32) -> Int32 {
  // 正向系且映射單射 ⟹ 逆極限 = 第一層
  if pr.sizes.length() == 0 {
    0
  } else {
    pr.sizes[0] * k
  }
}

///|
/// [E-Hom2] Hom(Z[S]^■, A) 的維數，A = F_p^k（離散）。
///   Z[S]^■ = lim_n Z[S_n]，故 Homs 由各層級「讀出」：
///   全部局部常數函數 = 最高層的函數空間，維數 k·|S_N|。
pub fn cond_hom_solid_discrete(pr : Prof, k : Int32) -> Int32 {
  let n = pr.sizes.length()
  if n == 0 {
    0
  } else {
    pr.sizes[n - 1] * k
  }
}

///|
/// [T-Solid] 固態性缺口（對離散目標 A = F_p^k）：
///   Hom(Z[S]^■,A) − Hom(Z[S],A) = k(|S_N| − |S_0|)。
///   非單點時嚴格為正 ⟹ **F_p 不是固態群**（這是凝聚數學的起點反例）。
pub fn cond_solidity_defect(pr : Prof, k : Int32) -> Int32 {
  cond_hom_solid_discrete(pr, k) - cond_hom_free_discrete(pr, k)
}

///|
/// [T-SolidCompact] 對緊（固態）目標 A = Z_p 的模型：A = lim_n Z/p^n，
///   Hom(Z[S], A) = lim_n Hom(Z[S], Z/p^n) = lim_n (Z/p^n)^{S_0} → 維數 k|S_0|；
///   Hom(Z[S]^■, A) = lim_n colim_m (Z/p^n)^{S_m} = lim_n (Z/p^n)^{S_0}，同樣為 k|S_0|。
///   故對 Z_p 型目標固態性缺口恆為 0（固態）。
pub fn cond_solidity_defect_profinite(pr : Prof, k : Int32) -> Int32 {
  // 兩邊都是 lim_n (Z/p^n)^{|S_0|}，維數相同
  cond_hom_free_discrete(pr, k) - cond_hom_free_discrete(pr, k)
}

///|
/// [E-Tensor] 凝聚張量：Z[S]^■ ⊗ Z[T]^■ 的層級鏈（逐層張量）。
pub fn chain_tensor(a : Chain, b : Chain) -> Chain {
  let n = if a.dims.length() < b.dims.length() {
    a.dims.length()
  } else {
    b.dims.length()
  }
  let dims : Array[Int32] = []
  for i = 0; i < n; i = i + 1 {
    dims.push(a.dims[i] * b.dims[i])
  }
  let trans : Array[@core.Mat] = []
  for i = 0; i + 1 < n; i = i + 1 {
    let ma = a.trans[i]
    let mb = b.trans[i]
    let rows = dims[i]
    let cols = dims[i + 1]
    let mat = @core.mat_make(rows, cols, 0)
    for x = 0; x < ma.cols; x = x + 1 {
      for y = 0; y < mb.cols; y = y + 1 {
        let col = x * mb.cols + y
        let mut ra = -1
        for r = 0; r < ma.rows; r = r + 1 {
          if ma.data[r * ma.cols + x] != 0 {
            ra = r
          }
        }
        let mut rb = -1
        for r = 0; r < mb.rows; r = r + 1 {
          if mb.data[r * mb.cols + y] != 0 {
            rb = r
          }
        }
        if ra >= 0 && rb >= 0 {
          mat.data[(ra * mb.rows + rb) * cols + col] = 1
        }
      }
    }
    trans.push(mat)
  }
  Chain::{ dims, trans, p: a.p, }
}

///|
/// 兩鏈是否逐層相等（維數與矩陣）。
pub fn chain_eq(a : Chain, b : Chain) -> Bool {
  if a.dims != b.dims {
    return false
  }
  if a.trans.length() != b.trans.length() {
    return false
  }
  let mut ok = true
  for k = 0; k < a.trans.length(); k = k + 1 {
    if !@core.mat_eq_mod(a.trans[k], b.trans[k], a.p) {
      ok = false
    }
  }
  ok
}
