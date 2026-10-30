// ============================================================================
// @tensorlab/ss —— 譜序列引擎（F_p 係數）：頁、微分、同調頁、退化、收斂、張量積
// ----------------------------------------------------------------------------
// 一個譜序列是一族 (E_r^{p,q}, d_r)，d_r : E_r^{p,q} → E_r^{p+r, q−r+1}，且 E_{r+1} = H(E_r, d_r)。
// 本引擎把「頁」實現為**有限矩形視窗**內的有限維 F_p 向量空間：
//   dims[i][j] = dim E^{p0+i, q0+j}，d[i][j] 是 d_r 在該格的矩陣（目標維 × 來源維）。
//
//   [D-Page]      一頁 = 維數表 + 微分矩陣表
//   [T-SS-DD]     d_r ∘ d_r = 0（在相鄰兩格上驗證）
//   [E-PageNext]  E_{r+1}^{p,q} = ker d_r / im d_r，維數 = ker −im（秩–零化度）
//   [T-SS-Deg]    若某頁所有微分為零，則 E_∞ = 該頁
//   [T-SS-Edge]   邊緣：總維數 Σ_{p+q=n} E_∞^{p,q} ≥ dim H_n（有擴張問題時嚴格大於）
//   [E-Tensor]    兩譜序列的張量積頁（Künneth：域上無 Tor 項）
// ============================================================================

///|
/// [D-Page] 譜序列的一頁。視窗為 p ∈ [p0, p0+np−1]、q ∈ [q0, q0+nq−1]。
pub struct Page {
  r : Int32
  p0 : Int32
  q0 : Int32
  np : Int32
  nq : Int32
  dims : Array[Array[Int32]]
  d : Array[Array[@core.Mat?]]
  p : Int32
  /// q 方向：false ⟹ d_r: (p,q) → (p+r, q−r+1)（同調／餘調標準型）；
  /// true ⟹ d_r: (p,q) → (p+r, q+r−1)（Adams 譜序列型，q = 總度數）。
  qflip : Bool
}

///|
pub fn page_new(
  r : Int32,
  p0 : Int32,
  q0 : Int32,
  np : Int32,
  nq : Int32,
  p : Int32,
) -> Page {
  page_new_q(r, p0, q0, np, nq, p, false)
}

///|
/// 由 q 方向旗標建頁（Adams 譜序列用 true）。
pub fn page_new_q(
  r : Int32,
  p0 : Int32,
  q0 : Int32,
  np : Int32,
  nq : Int32,
  p : Int32,
  qflip : Bool,
) -> Page {
  let dims : Array[Array[Int32]] = Array::makei(np, _ => Array::make(nq, 0))
  let d : Array[Array[@core.Mat?]] = Array::makei(np, _ => {
    Array::makei(nq, _ => None)
  })
  Page::{ r, p0, q0, np, nq, dims, d, p, qflip, }
}

///|
pub fn page_in(page : Page, i : Int32, j : Int32) -> Bool {
  i >= 0 && i < page.np && j >= 0 && j < page.nq
}

///|
pub fn page_dim(page : Page, i : Int32, j : Int32) -> Int32 {
  if page_in(page, i, j) {
    page.dims[i][j]
  } else {
    0
  }
}

///|
/// 以絕對雙次 (p,q) 取維數。
pub fn page_dim_at(page : Page, p : Int32, q : Int32) -> Int32 {
  page_dim(page, p - page.p0, q - page.q0)
}

///|
pub fn page_setdim(page : Page, i : Int32, j : Int32, m : Int32) -> Unit {
  if page_in(page, i, j) {
    page.dims[i][j] = m
  }
}

///|
pub fn page_setd(page : Page, i : Int32, j : Int32, m : @core.Mat) -> Unit {
  if page_in(page, i, j) {
    page.d[i][j] = Some(m)
  }
}

///|
/// 以絕對雙次設定微分。
pub fn page_setd_at(page : Page, p : Int32, q : Int32, m : @core.Mat) -> Unit {
  page_setd(page, p - page.p0, q - page.q0, m)
}

///|
pub fn page_getd(page : Page, i : Int32, j : Int32) -> @core.Mat? {
  if page_in(page, i, j) {
    page.d[i][j]
  } else {
    None
  }
}

///|
/// 微分在 q 方向上的位移：標準型為 −(r−1)，Adams 型為 +(r−1)。
pub fn page_dq(page : Page) -> Int32 {
  if page.qflip {
    page.r - 1
  } else {
    -(page.r - 1)
  }
}

///|
/// d_r: (i,j) 的目標 q 索引。
pub fn page_target_q(page : Page, j : Int32) -> Int32 {
  j + page_dq(page)
}

///|
/// 目標格 (i,j) 的來源 q 索引（反向）。
pub fn page_source_q(page : Page, j : Int32) -> Int32 {
  j - page_dq(page)
}

///|
/// [T-SS-DD] d_r ∘ d_r = 0：對每一格 (i,j)，d_r(i+r, j−r+1) ∘ d_r(i,j) 必須為零矩陣。
pub fn page_dd_zero(page : Page) -> Bool {
  let mut ok = true
  for i = 0; i < page.np; i = i + 1 {
    for j = 0; j < page.nq; j = j + 1 {
      match page.d[i][j] {
        Some(m) =>
          match page_getd(page, i + page.r, page_target_q(page, j)) {
            Some(m2) =>
              if !@core.mat_is_zero(@core.mat_mul(m2, m, page.p)) {
                ok = false
              }
            None => ()
          }
        None => ()
      }
    }
  }
  ok
}

///|
/// 每一格的微分是否都為零（或不存在）。
pub fn page_zero_diffs(page : Page) -> Bool {
  let mut ok = true
  for i = 0; i < page.np; i = i + 1 {
    for j = 0; j < page.nq; j = j + 1 {
      match page.d[i][j] {
        Some(m) => if !@core.mat_is_zero(m) { ok = false }
        None => ()
      }
    }
  }
  ok
}

///|
/// dim ker d_r 於該格。
pub fn page_ker_dim(page : Page, i : Int32, j : Int32) -> Int32 {
  match page_getd(page, i, j) {
    Some(m) => m.cols - @core.rank_mod(m, @core.mk_field(page.p))
    None => page_dim(page, i, j)
  }
}

///|
/// dim im d_r（來源在 (i−r, j+r−1)）。
pub fn page_im_dim(page : Page, i : Int32, j : Int32) -> Int32 {
  match page_getd(page, i - page.r, page_source_q(page, j)) {
    Some(m) => @core.rank_mod(m, @core.mk_field(page.p))
    None => 0
  }
}

///|
/// [E-PageNext] E_{r+1}^{p,q} = ker d_r / im d_r 的維數。
pub fn page_hom_dim(page : Page, i : Int32, j : Int32) -> Int32 {
  page_ker_dim(page, i, j) - page_im_dim(page, i, j)
}

///|
/// [E-PageNext] 取下一頁：r+1，維數 = 上同調維數；微分留空（由呼叫者依幾何指定 d_{r+1}）。
pub fn page_next(page : Page) -> Page {
  let out = page_new_q(
    page.r + 1,
    page.p0,
    page.q0,
    page.np,
    page.nq,
    page.p,
    page.qflip,
  )
  for i = 0; i < page.np; i = i + 1 {
    for j = 0; j < page.nq; j = j + 1 {
      out.dims[i][j] = page_hom_dim(page, i, j)
    }
  }
  out
}

///|
/// 總次數 n 上的維數和 Σ_{p+q=n} E^{p,q}。
pub fn page_total(page : Page, n : Int32) -> Int32 {
  let mut s = 0
  for i = 0; i < page.np; i = i + 1 {
    for j = 0; j < page.nq; j = j + 1 {
      if page.p0 + i + (page.q0 + j) == n {
        s = s + page.dims[i][j]
      }
    }
  }
  s
}

///|
/// 由總次數 0 到 upper 的維數表。
pub fn page_totals(page : Page, upper : Int32) -> Array[Int32] {
  Array::makei(upper + 1, n => page_total(page, n))
}

///|
/// [T-SS-Edge] 收斂檢查：Σ_{p+q=n} E_∞^{p,q} 逐項 ≥ dim H_n；等式 ⟹ 無擴張問題。
///   回傳 (是否都 ≥, 是否逐項相等)。
pub fn page_converges(page : Page, target : Array[Int32]) -> (Bool, Bool) {
  let mut fit = true
  let mut exact = true
  for n = 0; n < target.length(); n = n + 1 {
    let s = page_total(page, n)
    if s < target[n] {
      fit = false
    }
    if s != target[n] {
      exact = false
    }
  }
  (fit, exact)
}

///|
/// [E-Tensor] 兩頁的張量積：E^{p,q} = ⊕_{p1+p2=p, q1+q2=q} E_1^{p1,q1} ⊗ E_2^{p2,q2}。
///   在域上 Künneth 無 Tor 項，故維數相乘並卷積。
pub fn page_tensor(a : Page, b : Page) -> Page {
  let np = a.np + b.np - 1
  let nq = a.nq + b.nq - 1
  let out = page_new_q(a.r, a.p0 + b.p0, a.q0 + b.q0, np, nq, a.p, a.qflip)
  for i = 0; i < np; i = i + 1 {
    for j = 0; j < nq; j = j + 1 {
      let mut s = 0
      for i1 = 0; i1 < a.np; i1 = i1 + 1 {
        for j1 = 0; j1 < a.nq; j1 = j1 + 1 {
          let i2 = i - i1
          let j2 = j - j1
          if page_in(b, i2, j2) {
            s = s + a.dims[i1][j1] * b.dims[i2][j2]
          }
        }
      }
      out.dims[i][j] = s
    }
  }
  out
}

///|
/// 平移一頁（懸掛用）：E^{p,q} ↦ E^{p+dp, q+dq}。
pub fn page_shift(a : Page, dp : Int32, dq : Int32) -> Page {
  let out = page_new_q(a.r, a.p0 + dp, a.q0 + dq, a.np, a.nq, a.p, a.qflip)
  for i = 0; i < a.np; i = i + 1 {
    for j = 0; j < a.nq; j = j + 1 {
      out.dims[i][j] = a.dims[i][j]
    }
  }
  out
}

///|
/// 頁的非零格個數（診斷用）。
pub fn page_support(page : Page) -> Int32 {
  let mut c = 0
  for i = 0; i < page.np; i = i + 1 {
    for j = 0; j < page.nq; j = j + 1 {
      if page.dims[i][j] > 0 {
        c = c + 1
      }
    }
  }
  c
}

///|
/// 一頁的維數表壓成字串（報告用）。
pub fn page_show(page : Page) -> String {
  let mut s = "r=\{page.r}"
  for i = 0; i < page.np; i = i + 1 {
    for j = 0; j < page.nq; j = j + 1 {
      if page.dims[i][j] > 0 {
        s = "\{s} (\{page.p0 + i},\{page.q0 + j})=\{page.dims[i][j]}"
      }
    }
  }
  s
}
