///| stwist —— 扭結構的超化：奇偶標記、Koszul 號 2-閉鏈、超中心、
///| （ℤ/2）^d 的 Betti 譜、分次正則表示的超特徵標。
///|
///|  * `[S-D-Parity]` 奇偶 p(a) = Σaᵢ mod 2 是群同態；
///|    Koszul 號 σ(a,b) = (−1)^{p(a)p(b)} 是 2-閉鏈（結合律）；
///|  * `[S-T-SignClass]` σ 在 H²(G, 𝔽₂) 中非平凡（d ≤ 3 窮舉 δμ = σ 無解）；
///|  * `[S-C-H2Betti]` Betti 譜：dim H^k((ℤ/2)^d, 𝔽₂) = C(d+k−1, k)
///|    （多項環 𝔽₂[x₁..x_d] 的成長——H¹=d、H²=C(d+1,2)、H³=C(d+2,3)）；
///|  * `[S-T-SCenter]` 號代數（ω=0＋Koszul 號）：普通中心 = 全空間（交換！），
///|    超中心 = 偶部（dim 2^{d−1}）——「交換但不超交換」；
///|  * `[S-T-NoGoCenter]` 非平凡 ω 上加 Koszul 號：超中心 = 中心 = rad(b_ω)
///|    （同態奇偶的號在交換子中相消——No-Go：特徵標分次不改變中心）；
///|  * `[S-C-GrTrace]` 分次正則表示的超特徵標恆為 0（Witten 指標消失），
///|    而普通特徵標 tr(L_a) = |G|·δ_{a,0} 非平凡——譜上的「分次隱形」。

///| [S-D-Parity] G = ∏ℤ/nᵢ 的奇偶（各 nᵢ 為偶時是良定義的同態）。
pub fn parity(g : @twist.Grp, a : Int) -> Int {
  let v = @twist.grp_of_code(g, a)
  let mut s = 0
  for x in v {
    s = s + x
  }
  s % 2
}

///| Koszul 號 σ(a,b) = (−1)^{p(a)p(b)} ∈ {1, −1}（mod p 表成 1 / p−1）。
pub fn sign_sigma(g : @twist.Grp, a : Int, b : Int, p : Int) -> Int {
  if parity(g, a) * parity(g, b) % 2 == 1 {
    p - 1
  } else {
    1
  }
}

///| 符號餘閉鏈條件（mod 2，加法記法）：σ(b,c)+σ(a,b+c) ≡ σ(a,b)+σ(a+b,c)。
///| 此處直接以 p(a)p(b) mod 2 驗證（= log_{−1} σ）。
pub fn sign_cocycle_holds(g : @twist.Grp, a : Int, b : Int, c : Int) -> Bool {
  let pa = parity(g, a)
  let pb = parity(g, b)
  let pc = parity(g, c)
  let pbc = (parity(g, @twist.grp_code(g, @twist.grp_add(g, @twist.grp_of_code(g, b), @twist.grp_of_code(g, c))))
  )
  let pab = (parity(g, @twist.grp_code(g, @twist.grp_add(g, @twist.grp_of_code(g, a), @twist.grp_of_code(g, b))))
  )
  (pb * pc + pa * pbc) % 2 == (pa * pb + pab * pc) % 2
}

///| [S-T-SignClass] 窮舉搜尋 μ: G → 𝔽₂ 使 δμ = p(·)p(·)（mod 2）；回傳 true 若找到。
pub fn sign_is_coboundary(g : @twist.Grp) -> Bool {
  let n = @twist.grp_order(g)
  // μ 由 0/1 向量給定（長度 n）；窮舉 2^n 個
  let mut code = 0
  let total = 1 << n
  while code < total {
    let mu : Array[Int] = Array::make(n, 0)
    let mut x = code
    let mut i = 0
    while i < n {
      mu[i] = x % 2
      x = x / 2
      i = i + 1
    }
    // 檢查 δμ(a,b) = μ(a)+μ(b)+μ(a+b) ≡ p(a)p(b)（char 2）
    let mut ok = true
    let mut a = 0
    while a < n && ok {
      let mut b = 0
      while b < n && ok {
        let ab = @twist.grp_code(
          g,
          @twist.grp_add(g, @twist.grp_of_code(g, a), @twist.grp_of_code(g, b)),
        )
        let lhs = (mu[a] + mu[b] + mu[ab]) % 2
        let rhs = parity(g, a) * parity(g, b) % 2
        if lhs != rhs {
          ok = false
        }
        b = b + 1
      }
      a = a + 1
    }
    if ok {
      return true
    }
    code = code + 1
  }
  false
}

// ------------------------------------------------------- 號扭曲代數 --
///| 分次扭曲群代數的資料：ω: G×G → ℤ/ℓ（乘法相位 ζ^ω）＋ Koszul 號。
pub struct SW {
  g : @twist.Grp
  ell : Int
  field : Int
  zeta : Int
  omega : Array[Int] // n×n，ω(a,b) mod ell
}

pub fn sw_of(g : @twist.Grp, ell : Int, field : Int, omega : Array[Int]) -> SW {
  SW::{ g, ell, field, zeta: @twist.primitive_root(ell, field), omega }
}

///| 雙線性餘閉鏈 ω(a,b) = Σ_{ij} c_{ij} aᵢbⱼ mod ℓ（c 為 d×d）。
pub fn bilinear_cocycle(g : @twist.Grp, ell : Int, field : Int, c : Array[Array[Int]]) -> SW {
  let n = @twist.grp_order(g)
  let omega : Array[Int] = Array::make(n * n, 0)
  let mut a = 0
  while a < n {
    let mut b = 0
    while b < n {
      let av = @twist.grp_of_code(g, a)
      let bv = @twist.grp_of_code(g, b)
      let mut s = 0
      let mut i = 0
      while i < av.length() {
        let mut j = 0
        while j < bv.length() {
          s = s + c[i][j] * av[i] * bv[j]
          j = j + 1
        }
        i = i + 1
      }
      omega[a * n + b] = ((s % ell) + ell) % ell
      b = b + 1
    }
    a = a + 1
  }
  sw_of(g, ell, field, omega)
}

///| 乘法結構常數：e_a·e_b = ζ^{ω(a,b)}·σ(a,b)·e_{a+b}（在 F_field 中取值）。
pub fn sw_struct(s : SW, a : Int, b : Int) -> Int {
  let n = @twist.grp_order(s.g)
  let ph = @core.mod_pow(s.zeta, s.omega[a * n + b], s.field)
  ph * sign_sigma(s.g, a, b, s.field) % s.field
}

///| ω 的餘閉鏈條件（含號）逐三元組驗證。
pub fn sw_is_cocycle(s : SW) -> Bool {
  let g = s.g
  let n = @twist.grp_order(g)
  let p = s.field
  let mut a = 0
  while a < n {
    let mut b = 0
    while b < n {
      let mut c = 0
      while c < n {
        let bc = @twist.grp_code(g, @twist.grp_add(g, @twist.grp_of_code(g, b), @twist.grp_of_code(g, c)))
        let ab = @twist.grp_code(g, @twist.grp_add(g, @twist.grp_of_code(g, a), @twist.grp_of_code(g, b)))
        // (e_a e_b) e_c = e_a (e_b e_c)
        let l1 = sw_struct(s, a, b) * sw_struct(s, ab, c) % p
        let r1 = sw_struct(s, b, c) * sw_struct(s, a, bc) % p
        if l1 != r1 {
          return false
        }
        c = c + 1
      }
      b = b + 1
    }
    a = a + 1
  }
  true
}

///| rad(b_ω) = {a : ω(a,b) ≡ ω(b,a) ∀b}。
pub fn sw_radical_size(s : SW) -> Int {
  let n = @twist.grp_order(s.g)
  let mut cnt = 0
  let mut a = 0
  while a < n {
    let mut ok = true
    let mut b = 0
    while b < n {
      if s.omega[a * n + b] != s.omega[b * n + a] {
        ok = false
      }
      b = b + 1
    }
    if ok {
      cnt = cnt + 1
    }
    a = a + 1
  }
  cnt
}

///| 中心線性系統的核維數（ordinary；grade=false）或超中心（grade=true）。
///| 超中心條件：e_a 超中心 ⟺ ∀b：ζ^{ω(a,b)}σ(a,b) = (−1)^{p(a)p(b)}ζ^{ω(b,a)}σ(b,a)。
pub fn sw_center_dim(s : SW, graded : Bool) -> Int {
  let n = @twist.grp_order(s.g)
  let p = s.field
  let rows : Array[Array[Int]] = []
  let mut b = 0
  while b < n {
    let mut c = 0
    while c < n {
      // 比較 e_c 係數：z·e_b（變數 a = c−b）vs ±e_b·z
      let a = @twist.grp_code(
        s.g,
        @twist.grp_add(s.g, @twist.grp_of_code(s.g, c), @twist.grp_neg(s.g, @twist.grp_of_code(s.g, b))),
      )
      let row : Array[Int] = Array::make(n, 0)
      let lhs = sw_struct(s, a, b)
      let rhs = sw_struct(s, b, a)
      let eff = if graded {
        if parity(s.g, a) * parity(s.g, b) % 2 == 1 {
          (p - rhs) % p
        } else {
          rhs
        }
      } else {
        rhs
      }
      let d = ((lhs - eff) % p + p) % p
      row[a] = d
      if d != 0 {
        let _ = rows.push(row)
      }
      c = c + 1
    }
    b = b + 1
  }
  let m = @core.mat_from_rows(rows)
  let f = @core.mk_field(p)
  n - @core.gauss_jordan(m, f).rank
}

///| gauge 擾動：ω ⟼ ω + δμ（δμ(a,b) = μ(a)+μ(b)−μ(a+b) mod ℓ）。
pub fn sw_gauge(s : SW, mu : Array[Int]) -> SW {
  let n = @twist.grp_order(s.g)
  let w : Array[Int] = Array::make(n * n, 0)
  let mut a = 0
  while a < n {
    let mut b = 0
    while b < n {
      let ab = @twist.grp_code(
        s.g,
        @twist.grp_add(s.g, @twist.grp_of_code(s.g, a), @twist.grp_of_code(s.g, b)),
      )
      let dv = ((mu[a] + mu[b] - mu[ab]) % s.ell + s.ell) % s.ell
      w[a * n + b] = ((s.omega[a * n + b] + dv) % s.ell + s.ell) % s.ell
      b = b + 1
    }
    a = a + 1
  }
  SW::{ g: s.g, ell: s.ell, field: s.field, zeta: s.zeta, omega: w }
}

///| b_ω(a,b) = ω(a,b) − ω(b,a) mod ℓ 是否為雙線性（隨機抽查）。
pub fn b_omega_bilinear(s : SW) -> Bool {
  let g = s.g
  let n = @twist.grp_order(g)
  let add = fn(x : Int, y : Int) -> Int {
    @twist.grp_code(g, @twist.grp_add(g, @twist.grp_of_code(g, x), @twist.grp_of_code(g, y)))
  }
  let b = fn(x : Int, y : Int) -> Int {
    ((s.omega[x * n + y] - s.omega[y * n + x]) % s.ell + s.ell) % s.ell
  }
  let mut a1 = 0
  while a1 < n {
    let mut a2 = 0
    while a2 < n {
      let mut c = 0
      while c < n {
        // b(a1+a2, c) = b(a1,c)+b(a2,c)？
        if b(add(a1, a2), c) != (b(a1, c) + b(a2, c)) % s.ell {
          return false
        }
        c = c + 1
      }
      a2 = a2 + 1
    }
    a1 = a1 + 1
  }
  true
}

///| e_a 是否超中心（齊次條件，逐 b 驗證）。
pub fn sw_supercentral(s : SW, a : Int) -> Bool {
  let n = @twist.grp_order(s.g)
  let p = s.field
  let mut b = 0
  while b < n {
    // e_a e_b = (−1)^{p(a)p(b)} e_b e_a ?
    let lhs = sw_struct(s, a, b)
    let rhs = if parity(s.g, a) * parity(s.g, b) % 2 == 1 {
      (p - sw_struct(s, b, a)) % p
    } else {
      sw_struct(s, b, a)
    }
    if lhs != rhs {
      return false
    }
    b = b + 1
  }
  true
}

///| [S-C-GrTrace] 左正則表示 L_a 的（超）跡。
pub fn sw_reg_trace(s : SW, a : Int, graded : Bool) -> Int {
  let n = @twist.grp_order(s.g)
  let p = s.field
  let mut tr = 0
  let mut b = 0
  while b < n {
    // L_a e_b = sw_struct(a,b) e_{a+b}
    let ab = @twist.grp_code(
      s.g,
      @twist.grp_add(s.g, @twist.grp_of_code(s.g, a), @twist.grp_of_code(s.g, b)),
    )
    if ab == b {
      // a = 0（群為交換且 a+b=b ⟹ a=0）
      let w = if graded && parity(s.g, b) == 1 { p - 1 } else { 1 }
      tr = (tr + w) % p
    }
    b = b + 1
  }
  tr % p
}

// ------------------------------------------------------- H³ 與 Betti 譜 --
///| 非歸一化 δ²: C² → C³（列 = (a,b,c)，行變數 = (i,j)）。
pub fn d2_unnorm(g : @twist.Grp, ell : Int) -> @core.Mat {
  let n = @twist.grp_order(g)
  let add = fn(x : Int, y : Int) -> Int {
    @twist.grp_code(g, @twist.grp_add(g, @twist.grp_of_code(g, x), @twist.grp_of_code(g, y)))
  }
  @core.mat_build(n * n * n, n * n, (row, col) => {
    let a = row / (n * n)
    let b = (row / n) % n
    let c = row % n
    let i = col / n
    let j = col % n
    // δ²ω(a,b,c) = ω(b,c) − ω(a+b,c) + ω(a,b+c) − ω(a,b)
    let hit = fn(x : Int, y : Int, sgn : Int) -> Int {
      if x == i && y == j {
        sgn
      } else {
        0
      }
    }
    let v = hit(b, c, 1) - hit(add(a, b), c, 1) + hit(a, add(b, c), 1) - hit(a, b, 1)
    ((v % ell) + ell) % ell
  })
}

///| 非歸一化 δ³: C³ → C⁴（列 = (a,b,c,d)，行變數 = (i,j,k)）。
///| δ³f(a,b,c,d) = f(b,c,d) − f(a+b,c,d) + f(a,b+c,d) − f(a,b,c+d) + f(a,b,c)
pub fn d3_matrix(g : @twist.Grp, ell : Int) -> @core.Mat {
  let n = @twist.grp_order(g)
  let add = fn(x : Int, y : Int) -> Int {
    @twist.grp_code(g, @twist.grp_add(g, @twist.grp_of_code(g, x), @twist.grp_of_code(g, y)))
  }
  @core.mat_build(n * n * n * n, n * n * n, (row, col) => {
    let d0 = row / (n * n * n)
    let d1 = (row / (n * n)) % n
    let d2 = (row / n) % n
    let d3 = row % n
    let c0 = col / (n * n)
    let c1 = (col / n) % n
    let c2 = col % n
    let hit = fn(i0 : Int, i1 : Int, i2 : Int) -> Int {
      if i0 == c0 && i1 == c1 && i2 == c2 {
        1
      } else {
        0
      }
    }
    let v = hit(d1, d2, d3) -
      hit(add(d0, d1), d2, d3) +
      hit(d0, add(d1, d2), d3) -
      hit(d0, d1, add(d2, d3)) +
      hit(d0, d1, d2)
    ((v % ell) + ell) % ell
  })
}

///| dim H³ = nullity(δ³) − rank(δ²)（|G| ≤ 4 用）。
pub fn h3_dim(g : @twist.Grp, ell : Int) -> Int {
  let f = @core.mk_field(ell)
  let d3 = d3_matrix(g, ell)
  let d2 = d2_unnorm(g, ell)
  let n = @twist.grp_order(g)
  let dim3 = n * n * n
  let r3 = @core.rank_mod(d3, f)
  let r2 = @core.rank_mod(d2, f)
  (dim3 - r3) - r2
}

///| 對照組：零 2-閉鏈是否為餘邊界（μ ≡ 0 即可）。
pub fn sign_is_coboundary_zero(g : @twist.Grp) -> Bool {
  let n = @twist.grp_order(g)
  let mu : Array[Int] = Array::make(n, 0)
  let mut a = 0
  while a < n {
    let mut b = 0
    while b < n {
      let ab = @twist.grp_code(
        g,
        @twist.grp_add(g, @twist.grp_of_code(g, a), @twist.grp_of_code(g, b)),
      )
      if (mu[a] + mu[b] + mu[ab]) % 2 != 0 {
        return false
      }
      b = b + 1
    }
    a = a + 1
  }
  true
}
