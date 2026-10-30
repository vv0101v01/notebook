// ===========================================================================
// ahss — 扭曲 Atiyah–Hirzebruch 譜序列（twisted AHSS）
//
// E_2^{p,q} = H^p(X; KU_q)，d_3 = Sq³ + H ∪ (−)，H ∈ H³(X;Z) 為 twist 類。
// 本檔把 H^*(X;F_p) 當成**顯式分次代數**（維數 + 乘法表）真算：
//   • 杯積算子 H∪(−) 的矩陣；
//   • 引擎的標準雙次約定下 d_r 的雙次是 (r, 1−r)，故 d_3 的雙次是 (3, −2)；
//   • Sq³ 的消失證書（不穩定性：deg x ≤ 2 ⟹ Sq³x = 0；deg x ≥ 3 且
//     dim X ≤ 5 ⟹ Sq³x ∈ H^{≥6} = 0）。
// ===========================================================================

///|
/// [D-Alg] 有限維分次 F_p-代數（H^*(X;F_p) 的模型）。
///   `cup[i][j]`：H^i ⊗ H^j → H^{i+j}，列 = H^{i+j} 的基、欄 = a*dims[j] + b。
pub struct Alg {
  top : Int32
  dims : Array[Int32]
  cup : Array[Array[@core.Mat?]]
  p : Int32
}

///|
/// 空骨架。
pub fn alg_skeleton(dims : Array[Int32], p : Int32) -> Alg {
  let n = dims.length()
  let cup : Array[Array[@core.Mat?]] = Array::makei(n, _ => {
    Array::makei(n, _ => None)
  })
  Alg::{ top: n - 1, dims, cup, p, }
}

///|
/// 設定一塊乘法。
pub fn alg_set_cup(a : Alg, i : Int32, j : Int32, m : @core.Mat) -> Unit {
  a.cup[i][j] = Some(m)
}

///|
/// 取一塊乘法（缺省為零矩陣）。
pub fn alg_get_cup(a : Alg, i : Int32, j : Int32) -> @core.Mat {
  if i < 0 || j < 0 || i > a.top || j > a.top || i + j > a.top {
    return @core.mat_make(0, 0, 0)
  }
  match a.cup[i][j] {
    Some(m) => m
    None => @core.mat_make(a.dims[i + j], a.dims[i] * a.dims[j], 0)
  }
}

///|
/// 度數 k 的維數。
pub fn alg_dim(a : Alg, k : Int32) -> Int32 {
  if k < 0 || k > a.top {
    0
  } else {
    a.dims[k]
  }
}

// ---------------------------------------------------------------------------
// 具體代數：外代數、張量積、多項式（平方零）
// ---------------------------------------------------------------------------

///|
/// [D-Wedge] 外代數 Λ(x_1,…,x_g)，生成元度數 `degs`（F_2：無符號）。
///   基 = 生成元子集，依 (度數, 位元遮罩) 排序。
pub fn alg_wedge(degs : Array[Int32], p : Int32) -> Alg {
  let g = degs.length()
  let total = 1 << g
  let sdeg : Array[Int32] = Array::make(total, 0)
  let mut top = 0
  for m = 0; m < total; m = m + 1 {
    let mut d = 0
    for i = 0; i < g; i = i + 1 {
      if (m >> i) % 2 == 1 {
        d = d + degs[i]
      }
    }
    sdeg[m] = d
    if d > top {
      top = d
    }
  }
  let blist : Array[Array[Int32]] = Array::makei(top + 1, _ => [])
  for m = 0; m < total; m = m + 1 {
    blist[sdeg[m]].push(m)
  }
  let dims : Array[Int32] = Array::makei(top + 1, k => blist[k].length())
  let alg = alg_skeleton(dims, p)
  for i = 0; i <= top; i = i + 1 {
    for j = 0; i + j <= top; j = j + 1 {
      let cols = dims[i] * dims[j]
      let m = @core.mat_make(dims[i + j], cols, 0)
      for a = 0; a < dims[i]; a = a + 1 {
        for b = 0; b < dims[j]; b = b + 1 {
          let s = blist[i][a]
          let t = blist[j][b]
          if (s & t) == 0 {
            let u = s + t
            for c = 0; c < dims[i + j]; c = c + 1 {
              if blist[i + j][c] == u {
                m.data[c * cols + a * dims[j] + b] = 1
              }
            }
          }
        }
      }
      alg_set_cup(alg, i, j, m)
    }
  }
  alg
}

///|
/// [D-Tensor] 張量代數 (A ⊗ B)：H^k = ⊕_{i+j=k} H^i(A) ⊗ H^j(B)。
///   H^k 的基元素記為三元組 (i, ia, ib)。
pub fn alg_tensor(a : Alg, b : Alg) -> Alg {
  let top = a.top + b.top
  let dims : Array[Int32] = Array::make(top + 1, 0)
  for k = 0; k <= top; k = k + 1 {
    for i = 0; i <= k; i = i + 1 {
      dims[k] = dims[k] + alg_dim(a, i) * alg_dim(b, k - i)
    }
  }
  let alg = alg_skeleton(dims, a.p)
  let tris : Array[Array[Array[Int32]]] = Array::makei(top + 1, k => {
    let arr : Array[Array[Int32]] = []
    for i = 0; i <= k; i = i + 1 {
      for ia = 0; ia < alg_dim(a, i); ia = ia + 1 {
        for ib = 0; ib < alg_dim(b, k - i); ib = ib + 1 {
          arr.push([i, ia, ib])
        }
      }
    }
    arr
  })
  for i = 0; i <= top; i = i + 1 {
    for j = 0; i + j <= top; j = j + 1 {
      let cols = dims[i] * dims[j]
      let m = @core.mat_make(dims[i + j], cols, 0)
      for pa = 0; pa < dims[i]; pa = pa + 1 {
        let ta = tris[i][pa]
        for pb = 0; pb < dims[j]; pb = pb + 1 {
          let tb = tris[j][pb]
          // A 分量：ta[1] · tb[1]，B 分量：ta[2] · tb[2]
          let ma = alg_get_cup(a, ta[0], tb[0])
          let mb = alg_get_cup(b, ta[2], tb[2])
          for ca = 0; ca < ma.rows; ca = ca + 1 {
            if ma.data[ca * ma.cols + ta[1] * alg_dim(a, tb[0]) + tb[1]] != 0 {
              for cb = 0; cb < mb.rows; cb = cb + 1 {
                if mb.data[cb * mb.cols + ta[2] * alg_dim(b, tb[2]) + tb[2]] !=
                  0 {
                  // 目標三元組：度數 ta[0]+tb[0]，A 基 ca，B 基 cb
                  for c = 0; c < dims[i + j]; c = c + 1 {
                    let t = tris[i + j][c]
                    if t[0] == ta[0] + tb[0] && t[1] == ca && t[2] == cb {
                      m.data[c * cols + pa * dims[j] + pb] = (
                          m.data[c * cols + pa * dims[j] + pb] + 1
                        ) %
                        a.p
                    }
                  }
                }
              }
            }
          }
        }
      }
      alg_set_cup(alg, i, j, m)
    }
  }
  alg
}

///|
/// 克羅內克積。
pub fn kron(a : @core.Mat, b : @core.Mat, p : Int32) -> @core.Mat {
  let rows = a.rows * b.rows
  let cols = a.cols * b.cols
  let m = @core.mat_make(rows, cols, 0)
  for i = 0; i < a.rows; i = i + 1 {
    for j = 0; j < a.cols; j = j + 1 {
      let v = a.data[i * a.cols + j]
      if v != 0 {
        for r = 0; r < b.rows; r = r + 1 {
          for c = 0; c < b.cols; c = c + 1 {
            let w = b.data[r * b.cols + c]
            if w != 0 {
              m.data[(i * b.rows + r) * cols + (j * b.cols + c)] = v * w % p
            }
          }
        }
      }
    }
  }
  m
}

///|
/// 單位矩陣。
pub fn id_mat(n : Int32) -> @core.Mat {
  let m = @core.mat_make(n, n, 0)
  for i = 0; i < n; i = i + 1 {
    m.data[i * n + i] = 1
  }
  m
}

///|
/// [T-Assoc] 結合律機器驗證：(xy)z = x(yz) 對所有基元素成立。
pub fn alg_check_assoc(a : Alg) -> Bool {
  let mut ok = true
  for i = 0; i <= a.top; i = i + 1 {
    for j = 0; i + j <= a.top; j = j + 1 {
      for k = 0; i + j + k <= a.top; k = k + 1 {
        let left = @core.mat_mul(
          alg_get_cup(a, i + j, k),
          kron(alg_get_cup(a, i, j), id_mat(a.dims[k]), a.p),
          a.p,
        )
        let right = @core.mat_mul(
          alg_get_cup(a, i, j + k),
          kron(id_mat(a.dims[i]), alg_get_cup(a, j, k), a.p),
          a.p,
        )
        if !@core.mat_eq_mod(left, right, a.p) {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// [T-Unit] 單位元檢查：deg 0 的唯一類 1 滿足 1·x = x = x·1。
pub fn alg_check_unit(a : Alg) -> Bool {
  if a.dims[0] != 1 {
    return false
  }
  let mut ok = true
  for j = 0; j <= a.top; j = j + 1 {
    let m = alg_get_cup(a, 0, j)
    let want = id_mat(a.dims[j])
    if !@core.mat_eq_mod(m, want, a.p) {
      ok = false
    }
  }
  ok
}

// ---------------------------------------------------------------------------
// 杯積算子與扭曲 d_3
// ---------------------------------------------------------------------------

///|
/// [E-CupOp] 以類 h ∈ H^{hdeg} 作杯積的算子：M_p : H^p → H^{p+hdeg}。
///   回傳長度 top+1 的陣列（超出範圍者為 0×0）。
pub fn cup_operator(a : Alg, hdeg : Int32, hclass : Int32) -> Array[@core.Mat] {
  let out : Array[@core.Mat] = []
  for i = 0; i <= a.top; i = i + 1 {
    if i + hdeg > a.top || i + hdeg < 0 {
      out.push(@core.mat_make(0, 0, 0))
    } else {
      let full = alg_get_cup(a, i, hdeg)
      // 取 h 對應的欄，組出矩陣
      let m = @core.mat_make(a.dims[i + hdeg], a.dims[i], 0)
      for r = 0; r < a.dims[i + hdeg]; r = r + 1 {
        for c = 0; c < a.dims[i]; c = c + 1 {
          m.data[r * a.dims[i] + c] = full.data[r * full.cols +
            c * a.dims[hdeg] +
            hclass]
        }
      }
      out.push(m)
    }
  }
  out
}

///|
/// 算子陣列是否全零。
pub fn ops_is_zero(ops : Array[@core.Mat]) -> Bool {
  let mut ok = true
  for m in ops {
    if !@core.mat_is_zero(m) {
      ok = false
    }
  }
  ok
}

///|
/// [T-Sq3] Sq³ 在 dim X ≤ 5 時必然為零：
///   deg x ≤ 2 時由不穩定性 Sq^i x = 0 (i > |x|)；deg x ≥ 3 時 Sq³x ∈ H^{≥6} = 0。
pub fn sq3_vanishes(a : Alg) -> Bool {
  a.top <= 5
}

///|
/// [E-AhssPage] 建 AHSS 的 E_2 頁：維數 dims[p][q−qlo] = dim H^p(X)（當 q 為容許的
///   K-理論度數時），其餘為 0。第二個索引就是係數度數 q（標準雙次約定）。
pub fn ahss_page(
  a : Alg,
  coeff_qs : Array[Int32],
  qlo : Int32,
  qhi : Int32,
) -> @ss.Page {
  let np = a.top + 1
  let nq = qhi - qlo + 1
  let page = @ss.page_new(3, 0, qlo, np, nq, a.p)
  for i = 0; i < np; i = i + 1 {
    for j = 0; j < nq; j = j + 1 {
      let q = qlo + j
      let mut ok = false
      for c in coeff_qs {
        if c == q {
          ok = true
        }
      }
      if ok {
        page.dims[i][j] = a.dims[i]
      }
    }
  }
  page
}

///|
/// 兩個算子陣列相加（F_p 上逐項模加）。
pub fn ahss_add_ops(
  x : Array[@core.Mat],
  y : Array[@core.Mat],
) -> Array[@core.Mat] {
  let out : Array[@core.Mat] = []
  for i = 0; i < x.length(); i = i + 1 {
    let a = x[i]
    let b = if i < y.length() { y[i] } else { @core.mat_make(0, 0, 0) }
    let m = @core.mat_make(a.rows, a.cols, 0)
    for r = 0; r < a.rows; r = r + 1 {
      for c = 0; c < a.cols; c = c + 1 {
        let mut v = a.data[r * a.cols + c]
        if r < b.rows && c < b.cols {
          v = v + b.data[r * b.cols + c]
        }
        m.data[r * a.cols + c] = v % 2
      }
    }
    out.push(m)
  }
  out
}

///|
/// 扭曲算子：H∪(−)（H 為 H^{hdeg} 的第 hclass 個基類）。
pub fn ahss_twist_ops(
  a : Alg,
  hdeg : Int32,
  hclass : Int32,
) -> Array[@core.Mat] {
  cup_operator(a, hdeg, hclass)
}

///|
/// 形狀正確的全零算子陣列（未扭曲時的 Sq³ / twist 都可以用它）。
pub fn ahss_zero_ops(a : Alg) -> Array[@core.Mat] {
  let out : Array[@core.Mat] = []
  for i = 0; i <= a.top; i = i + 1 {
    out.push(@core.mat_make(alg_dim(a, i + 3), alg_dim(a, i), 0))
  }
  out
}

///|
/// [E-AhssD3] 把 d_3 的算子裝進頁面：對每一格 (p,q)（維數 > 0 且目標在範圍內）
///   放入 ops[p]: H^p → H^{p+3}。引擎的標準雙次約定下目標是 (p+3, q−2)。
pub fn ahss_set_d3(page : @ss.Page, ops : Array[@core.Mat]) -> Unit {
  for i = 0; i < page.np; i = i + 1 {
    for j = 0; j < page.nq; j = j + 1 {
      if page.dims[i][j] > 0 && i + page.r < page.np && j - page.r + 1 >= 0 {
        if i < ops.length() {
          page.d[i][j] = Some(ops[i])
        }
      }
    }
  }
}
