///| smetric —— 度量結構的譜化／超化：圖 Laplacian 的 mod-p 譜論、
/// Vietoris–Rips 條碼、Hodge 分解（上／下 Laplacian 的核 = 同調）、
/// 以及「譜不決定度量」的否定性結果（同譜不同構）。
///|
///|  * `[S-D-CycLap]` 環圖 Laplacian L = 2I − A：連通 ⟹ λ=0 單根、
///    tr(L) = 2n、tr(L²) = 6n、偶 n 的 λ_max = 4、不同特徵值數 = ⌊n/2⌋+1；
///|  * `[S-T-LapNullity]` mod-p 零維數定理：nullity(L(C_n)) = 1 + [p | n]
///    （解空間 v_i = α + βi，β 自由 ⟺ p | n——mod-p 譜流的具體化身）；
///|  * `[S-NEG-Cospectral]` K_{1,4} 與 C₄∪K₁ 同譜（charpoly 相同）但不同構、
///    度量結構不同 ⟹ 譜資料無法恢復度量（譜 Gromov–Hausdorff 的失敗）；
///|  * `[S-D-VRBar]` VR 條碼：r = 0 ⟹ β = (n, 0)；r = 1 ⟹ β = (1, 1)
///    （圓圈誕生）、χ = 0；
///|  * `[S-D-Hodge]` Hodge：β₁ = dim ker(B₁ᵀB₁ + B₂B₂ᵀ)（帶號 mod p）
///    與 VR 消去法算出的 β₁ 逐點一致（n = 4..8、r = 1, 2）。

///| 環圖 Laplacian L = 2I − A（mod p）。
pub fn cycle_lap(n : Int, p : Int) -> @core.Mat {
  let a = @snc.cycle_adj(n, p)
  @core.mat_build(n, n, (i, j) => {
    let diag = if i == j { 2 % p } else { 0 }
    let v = diag - a.data[i * n + j]
    ((v % p) + p) % p
  })
}

///| 完全二部星圖 K_{1,4} 的鄰接矩陣（中心 = 0 號點）。
pub fn star_adj(p : Int) -> @core.Mat {
  @core.mat_build(5, 5, (i, j) => {
    if (i == 0 && j > 0) || (j == 0 && i > 0) {
      1 % p
    } else {
      0
    }
  })
}

///| C₄ ∪ K₁（不連通）的鄰接矩陣。
pub fn c4_plus_iso_adj(p : Int) -> @core.Mat {
  @core.mat_build(5, 5, (i, j) => {
    if i < 4 && j < 4 && (j == (i + 1) % 4 || j == (i + 3) % 4) {
      1 % p
    } else {
      0
    }
  })
}

///| 矩陣的（mod p）零空間維數。
pub fn nullity_mod(a : @core.Mat, p : Int) -> Int {
  let f = @core.mk_field(p)
  a.rows - @core.rank_mod(a, f)
}

// ------------------------------------------------------------- VR / Hodge --
///| VR 複形的帶號邊界矩陣 B_k（mod p；以頂點排序定向）。
///| sims：全部單純形（各為升冪頂點列表）；回傳 B_k：(k+1)−單純形 × k−單純形。
pub fn signed_boundary(
  sims : Array[Array[Int]],
  k : Int,
  p : Int,
) -> @core.Mat {
  // 列 = k+1 單純形（大小 k+1），行變數 = k 單純形（大小 k）
  let hi : Array[Array[Int]] = []
  for s in sims {
    if s.length() == k + 1 {
      let _ = hi.push(s)
    }
  }
  let lo : Array[Array[Int]] = []
  for s in sims {
    if s.length() == k {
      let _ = lo.push(s)
    }
  }
  let idx : Map[String, Int] = Map([])
  for i = 0; i < lo.length(); i = i + 1 {
    let mut key = ""
    for v in lo[i] {
      key = "\{key},\{v}"
    }
    idx[key] = i
  }
  @core.mat_build(hi.length(), lo.length(), (r, c) => {
    let s = hi[r]
    // ∂s = Σ_j (−1)^j · s \ {s_j}
    let mut val = 0
    for j = 0; j < s.length(); j = j + 1 {
      let face : Array[Int] = []
      for q = 0; q < s.length(); q = q + 1 {
        if q != j {
          let _ = face.push(s[q])
        }
      }
      let mut key = ""
      for v in face {
        key = "\{key},\{v}"
      }
      let col = idx.get(key)
      if col is Some(cc) {
        if cc == c {
          let sgn = if j % 2 == 1 { p - 1 } else { 1 }
          val = (val + sgn) % p
        }
      }
    }
    ((val % p) + p) % p
  })
}

///| Hodge：1-上鏈的 up+down Laplacian L₁ = B₁ᵀB₁ + B₂B₂ᵀ（mod p）。
pub fn hodge_l1(m : @metric.MSpace, r : Int, p : Int) -> @core.Mat? {
  let sims = @metric.vr_simplices(m, r)
  let b1 = signed_boundary(sims, 1, p) // 邊 × 頂點？：k=1 ⟹ (2-單純形=邊) × (1-單純形=點)
  let b2 = signed_boundary(sims, 2, p) // 三角形 × 邊
  // 維度檢查：b1 應為 邊×點；b2 為 三角×邊
  let ne = b1.rows
  if b2.cols != ne {
    return None
  }
  // b1 = 邊×點、b2 = 三角×邊 ⟹ L₁(邊) = b1·b1ᵀ + b2ᵀ·b2
  let b1t = @core.mat_transpose(b1)
  let b2t = @core.mat_transpose(b2)
  let l1 = @core.mat_add(@core.mat_mul(b1, b1t, p), @core.mat_mul(b2t, b2, p), p)
  Some(l1)
}

///| Hodge β₁：dim ker L₁（mod p）。
pub fn hodge_beta1(m : @metric.MSpace, r : Int, p : Int) -> Int? {
  let l1 = hodge_l1(m, r, p)
  if l1 is Some(mat) {
    Some(nullity_mod(mat, p))
  } else {
    None
  }
}
