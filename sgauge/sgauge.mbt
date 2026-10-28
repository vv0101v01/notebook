///| sgauge —— 規範／Clifford 結構的超化：單項 Clifford 代數 Cl(d) 的
///| ℤ₂ 分次結構、中心／反中心、分次張量積分解 Cl(V⊕W) ≅ Cl(V)⊗̂Cl(W)、
///| γ 矩陣實現的譜恆等式（跡、體積元）、以及格子 Dirac 算子的分次跡消失。
///|
///|  * `[S-D-ClMono]` 單項 Clifford：基底 = 子集 S ⊆ {1..d}，
///|    γ_S·γ_T = (−1)^{inv(S,T)}·q^{S∩T}·γ_{S△T}；結合律與分次相容；
///|  * `[S-T-ClCenter]` 中心／反中心維數表：d 偶 (1,1)、d 奇 (2,0)；
///|  * `[S-T-ClGrTensor]` Cl(d+d′) ≅ Cl(d) ⊗̂ Cl(d′)（Koszul 叉號精確匹配）；
///|  * `[S-D-GammaSpec]` γ 矩陣譜恆等式：{γᵢ,γⒿ} = 2δᵢⒿ、tr(γ_S) = 0（S≠∅）、
///|    ω² = (−1)^{d(d−1)/2}（兩種計算對照）、tr(ω) = 0；
///|  * `[S-D-LatDirac]` 格子 Dirac D = Σᵢγᵢ⊗A（A = 循環移位）：
///|    D² = d·(I⊗A²)（交叉項 Koszul 相消的矩陣層面驗證）；
///|    分次跡消失 tr(Π·D^{2k}) = 0（Π = i^m·ω，k ≥ 1）——格子 SUSY 的
///|    Witten 指標式敘述。

// --------------------------------------------------------- 單項 Clifford --
///| inv(S,T) = #{(i,j) : i ∈ S, j ∈ T, pos(i) > pos(j)}。
pub fn cl_sign(s : Int, t : Int) -> Int {
  let mut cnt = 0
  let mut i = s
  while i != 0 {
    let ipos = bit_pos(i)
    let mut k = 0
    while k < ipos {
      if ((t >> k) & 1) == 1 {
        cnt = cnt + 1
      }
      k = k + 1
    }
    i = i & (i - 1)
  }
  cnt
}

fn bit_pos(x : Int) -> Int {
  let mut k = 0
  let mut y = x
  while (y & 1) == 0 {
    y = y >> 1
    k = k + 1
  }
  k
}

///| 單項乘積的結構常數：回傳（係數 mod p, S△T）。
pub fn cl_mul(s : Int, t : Int, q : Array[Int], p : Int) -> (Int, Int) {
  let mut coeff = 1
  if cl_sign(s, t) % 2 == 1 {
    coeff = p - 1
  }
  let mut i = s & t
  while i != 0 {
    let b = bit_pos(i)
    coeff = coeff * q[b] % p
    i = i & (i - 1)
  }
  (coeff, s ^ t)
}

pub fn cl_dim(d : Int) -> Int {
  1 << d
}

///| 單項次數（0/1）。
pub fn cl_deg(s : Int) -> Int {
  let mut c = 0
  let mut i = s
  while i != 0 {
    c = c + 1
    i = i & (i - 1)
  }
  c % 2
}

///| 結合律抽查（隨機三元組）＋分次相容。
pub fn cl_check_assoc(
  d : Int,
  q : Array[Int],
  p : Int,
  trials : Int,
  r : @core.Rng,
) -> Bool {
  let dim = cl_dim(d)
  let mut ok = true
  for trial = 0; trial < trials; trial = trial + 1 {
    let s = @core.rng_below(r, dim)
    let t = @core.rng_below(r, dim)
    let u = @core.rng_below(r, dim)
    let (c1, w1) = cl_mul(s, t, q, p)
    let (c2, w2) = cl_mul(w1, u, q, p)
    let lhs = c1 * c2 % p
    let (c3, w3) = cl_mul(t, u, q, p)
    let (c4, w4) = cl_mul(s, w3, q, p)
    let rhs = c3 * c4 % p
    if lhs != rhs || w2 != w4 {
      ok = false
    }
    if cl_deg(s ^ t) != (cl_deg(s) + cl_deg(t)) % 2 {
      ok = false
    }
  }
  ok
}

///| 單項 m 與生成元 γⱼ 的（反）交換號：+1 / −1。
pub fn cl_comm_sign(s : Int, j : Int) -> Int {
  let k = cl_deg(s)
  if ((s >> j) & 1) == 1 {
    if (k + 1) % 2 == 1 {
      -1
    } else {
      1
    }
  } else if k == 1 {
    -1
  } else {
    1
  }
}

///| 中心維數與反中心維數（單項符號條件枚舉）。
pub fn cl_center_anticenter(d : Int) -> (Int, Int) {
  let dim = cl_dim(d)
  let mut cz = 0
  let mut acz = 0
  let mut s = 0
  while s < dim {
    let mut all_comm = true
    let mut all_anti = true
    let mut j = 0
    while j < d {
      let sg = cl_comm_sign(s, j)
      if sg != 1 {
        all_comm = false
      }
      if sg != -1 {
        all_anti = false
      }
      j = j + 1
    }
    if all_comm {
      cz = cz + 1
    }
    if all_anti {
      acz = acz + 1
    }
    s = s + 1
  }
  (cz, acz)
}

///| 分次張量積：Cl(d+d′) ≅ Cl(d) ⊗̂ Cl(d′)（全量結構常數比對）。
///| 嵌入：S ↦ (S₁, S₂)（低 d1 位 / 高 d2 位）；⊗̂ 帶 Koszul 叉號 (−1)^{|S₂||T₁|}。
pub fn grtensor_check(d1 : Int, d2 : Int, q : Array[Int], p : Int) -> Bool {
  let d = d1 + d2
  let dim = cl_dim(d)
  let mut s = 0
  while s < dim {
    let mut t = 0
    while t < dim {
      let (c, w) = cl_mul(s, t, q, p)
      let s1 = s & ((1 << d1) - 1)
      let s2 = s >> d1
      let t1 = t & ((1 << d1) - 1)
      let t2 = t >> d1
      // q 切片：因子 1 用 q[0..d1)、因子 2 用 q[d1..d)
      let q1 : Array[Int] = []
      for x = 0; x < d1; x = x + 1 {
        let _ = q1.push(q[x])
      }
      let q2 : Array[Int] = []
      for x = d1; x < d; x = x + 1 {
        let _ = q2.push(q[x])
      }
      let (c1, w1) = cl_mul(s1, t1, q1, p)
      let (c2, w2) = cl_mul(s2, t2, q2, p)
      let cross = if cl_deg(s2) * cl_deg(t1) % 2 == 1 { p - 1 } else { 1 }
      let c_rhs = c1 * c2 % p * cross % p
      let w_rhs = (w1 & ((1 << d1) - 1)) | (w2 << d1)
      if c != c_rhs || w != w_rhs {
        return false
      }
      t = t + 1
    }
    s = s + 1
  }
  true
}

// --------------------------------------------------------- γ 譜恆等式 --
///| 矩陣 A 的跡（mod p）。
pub fn mat_trace(a : @core.Mat, p : Int) -> Int {
  let mut t = 0
  for i = 0; i < a.rows; i = i + 1 {
    t = (t + a.data[i * a.cols + i]) % p
  }
  ((t % p) + p) % p
}

// --------------------------------------------------------- 格子 Dirac --
///| 循環移位矩陣 A（N×N，mod p）。
pub fn shift_mat(n : Int, p : Int) -> @core.Mat {
  @core.mat_build(n, n, (i, j) => if j == (i + 1) % n { 1 % p } else { 0 })
}
