///| sradon —— Radon 結構的譜化／超化：仿射平面 𝔽_n² 上有限 Radon 變換 R 的
///| 奇異譜 {n, n²+n}、Sherman–Morrison 濾波（有限 FBP 的精確重構）、
///| 奇偶帶號 Radon 的譜不變性、以及 Parseval 型能量恆等式。
///|
///|  * `[S-D-RadSpec]` RᵀR = nI + J（J = 全 1）⟹
///|    charpoly(RRᵀ) = (x−n)^{n²−1}(x−n²−n)、charpoly(RᵀR) = xⁿ(x−n)^{n²−1}(x−n²−n)
///|    （n ∈ {2,3,5,7}，係數 mod 大素數 q）；
///|  * `[S-T-FBP]` Sherman–Morrison：(nI+J)^{-1} = (1/n)I − (1/(n²(n+1)))J；
///|    濾波反投影 f̃ = X·Rᵀ·(Rf) = f 精確重構（隨機 f）；
///|  * `[S-C-GradedRad]` 奇偶帶號 R̃ = D·R（D = ±1 對角）：
///|    譜不變（R̃ᵀR̃ = RᵀR）且帶號 FBP 仍精確重構；
///|  * `[S-T-RadEnergy]]` Σ_lines (Rf)² = n·Σ_points f² + (Σ_points f)²。

///| 仿射平面 𝔽_n² 的點（行主序）：點 k ↔ (x,y) = (k/n, k%n)。
pub fn npoints(n : Int) -> Int {
  n * n
}

///| 線族：x + m·y ≡ c（m, c ∈ 𝔿_n）與 y ≡ c（水平族）：
/// 線 idx = dir_idx·n + c；dir_idx = m（前 n 個）或 n（水平）。
pub fn nlines(n : Int) -> Int {
  n * (n + 1)
}

///| 點 (x,y) 是否在線 (dir, c) 上。
pub fn on_line(x : Int, y : Int, dir : Int, c : Int, n : Int) -> Bool {
  if dir < n {
    // x·1 + y·m ≡ c (mod n)
    let m = dir
    ((x + y * m - c) % n + n) % n == 0
  } else {
    // 水平族（法向 (0,1)）：y ≡ c
    ((y - c) % n + n) % n == 0
  }
}

///| Radon 矩陣 R（lines × points，0/1，mod q）。
pub fn radon_mat(n : Int, q : Int) -> @core.Mat {
  let pl = nlines(n)
  let pp = npoints(n)
  @core.mat_build(pl, pp, (l, pnt) => {
    let dir = l / n
    let c = l % n
    let x = pnt / n
    let y = pnt % n
    if on_line(x, y, dir, c, n) {
      1 % q
    } else {
      0
    }
  })
}

///| 奇偶帶號 Radon：R̃ = D·R，D_ll = (−1)^{dir(l)+c(l)}（mod q）。
pub fn radon_graded(n : Int, q : Int) -> @core.Mat {
  let pl = nlines(n)
  let pp = npoints(n)
  @core.mat_build(pl, pp, (l, pnt) => {
    let dir = l / n
    let c = l % n
    let x = pnt / n
    let y = pnt % n
    if on_line(x, y, dir, c, n) {
      if (dir + c) % 2 == 1 {
        (q - 1) % q
      } else {
        1 % q
      }
    } else {
      0
    }
  })
}

///| 全 1 矩陣。
pub fn ones_mat(sz : Int, q : Int) -> @core.Mat {
  @core.mat_build(sz, sz, (_i, _j) => 1 % q)
}

///| Sherman–Morrison 濾波 X = (1/n)I − (1/(n²(n+1)))J（mod q）。
pub fn sm_filter(n : Int, sz : Int, q : Int) -> @core.Mat {
  let inv_n = @core.mod_pow(n % q, q - 2, q)
  let denom = n % q * (n % q) % q * ((n + 1) % q) % q
  let inv_den = @core.mod_pow(denom, q - 2, q)
  @core.mat_build(sz, sz, (i, j) => {
    let diag = if i == j { inv_n } else { 0 }
    let jpart = (q - inv_den) % q
    (diag + jpart) % q
  })
}

///| 多項式乘法（係數數組 mod q）。
pub fn poly_mul(a : Array[Int], b : Array[Int], q : Int) -> Array[Int] {
  let out : Array[Int] = Array::make(a.length() + b.length() - 1, 0)
  for i = 0; i < a.length(); i = i + 1 {
    for j = 0; j < b.length(); j = j + 1 {
      out[i + j] = (out[i + j] + a[i] * b[j]) % q
    }
  }
  out
}

///| 冪：poly^e。
pub fn poly_pow(base : Array[Int], e : Int, q : Int) -> Array[Int] {
  let mut acc : Array[Int] = [1]
  for k = 0; k < e; k = k + 1 {
    acc = poly_mul(acc, base, q)
  }
  acc
}

///| 期望的 charpoly(RRᵀ) = (x−n)^{n²−1}·(x−n²−n)（係數 [c0..c_{n²}]）。
pub fn expect_rrt_charpoly(n : Int, q : Int) -> Array[Int] {
  let lin = [((q - n % q) % q + q) % q, 1] // x − n
  let big = [((q - (n * n + n) % q) % q + q) % q, 1] // x − (n²+n)
  let p1 = poly_pow(lin, n * n - 1, q)
  poly_mul(p1, big, q)
}
