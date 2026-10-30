// ===========================================================================
// canon —— 規範形的測試：每一條都在驗 (C1) 可算、(C2) 完備性、(C3) 不變性
// ===========================================================================

///|
/// 單位矩陣。
fn eye(n : Int32) -> @core.Mat {
  let m = @core.mat_make(n, n, 0)
  for i = 0; i < n; i = i + 1 {
    m.data[i * n + i] = 1
  }
  m
}

///|
/// 一個可逆的「剪切」矩陣：I + E_{0,1}（行列式恆為 1）。
fn shear(n : Int32, p : Int32) -> @core.Mat {
  let m = eye(n)
  m.data[0 * n + 1] = 1 % p
  m
}

///|
/// 由位元遮罩造圖的鄰接矩陣（F_p 係數）。
fn graph_from_edges(
  n : Int32,
  edges : Array[(Int32, Int32)],
  p : Int32,
) -> @core.Mat {
  let m = @core.mat_make(n, n, 0)
  for e in edges {
    m.data[e.0 * n + e.1] = 1 % p
    m.data[e.1 * n + e.0] = 1 % p
  }
  m
}

///|
/// [T-Canon-RREF] 列等價 ⟺ RREF 相同：窮舉 M_{2×3}(F_2)，
///   依 RREF 分組，組數必須等於 F_2³ 的子空間數 1 + 7 + 7 = 15。
test "RREF is a complete invariant of row space" {
  let seen : Array[Array[Int32]] = []
  for code = 0; code < 64; code = code + 1 {
    let m = @core.mat_make(2, 3, 0)
    let mut c = code
    for i = 0; i < 2; i = i + 1 {
      for j = 0; j < 3; j = j + 1 {
        m.data[i * 3 + j] = c % 2
        c = c / 2
      }
    }
    let r = @canon.flatten(@canon.canon_rref(m, 2))
    let mut dup = false
    for x in seen {
      if x == r {
        dup = true
      }
    }
    if !dup {
      seen.push(r)
    }
  }
  // dim 0: 1 個、dim 1: 7 個、dim 2: 7 個
  assert_eq(seen.length(), 15)
  // 冪等性：RREF(RREF(A)) = RREF(A)
  let a = @core.mat_from_rows([[1, 1, 0], [0, 1, 1]])
  assert_eq(
    @canon.flatten(@canon.canon_rref(@canon.canon_rref(a, 2), 2)),
    @canon.flatten(@canon.canon_rref(a, 2)),
  )
  // 同行空間的不同矩陣給同一 RREF
  let b = @core.mat_from_rows([[1, 1, 0], [1, 0, 1]]) // 兩列和 = (0,1,1)
  assert_eq(@canon.canon_rref_same(a, b, 2), true)
}

///|
/// [T-Canon-SNF] Smith 對角線是么模等價的完備不變量。
test "Smith normal form: unimodular equivalence and divisibility" {
  // 有撓率的例子：diag(2,3) 么模等價於 diag(1,6)
  let a = @core.mat_from_rows([[2, 0], [0, 3]])
  let b = @core.mat_from_rows([[1, 2], [0, 6]])
  assert_eq(@canon.canon_snf(a), @canon.canon_snf(b))
  // 秩不同 ⟹ 不同
  let c = @core.mat_from_rows([[1, 0], [0, 0]])
  assert_eq(@canon.canon_snf(a) == @canon.canon_snf(c), false)
  // 整除鏈：d₁ | d₂
  let dg = @canon.canon_snf(@core.mat_from_rows([[4, 6], [2, 8]]))
  assert_eq(dg.length() >= 2, true)
  if dg.length() >= 2 {
    assert_eq(dg[1] % dg[0], 0)
  }
}

///|
/// [T-Canon-HNF] 整數列格的規範形：同一個格 ⟺ 同一個 HNF。
test "Hermite normal form is a complete invariant of a lattice" {
  // 同一個格：(1,2), (0,6) 與 (1,2), (2,10) = 2·(1,2) + (0,6)
  let a = @core.mat_from_rows([[1, 2], [0, 6]])
  let b = @core.mat_from_rows([[1, 2], [2, 10]])
  assert_eq(
    @canon.flatten(@canon.canon_hnf(a)),
    @canon.flatten(@canon.canon_hnf(b)),
  )
  // 不同的格
  let c = @core.mat_from_rows([[2, 0], [0, 1]])
  assert_eq(
    @canon.flatten(@canon.canon_hnf(a)) == @canon.flatten(@canon.canon_hnf(c)),
    false,
  )
  // 單列的格：生成元只差 ±1（唯一），故正規化為「首個非零為正」的同一向量
  let d = @core.mat_from_rows([[6, 9]])
  assert_eq(@canon.flatten(@canon.canon_hnf(d)), [6, 9])
  assert_eq(
    @canon.flatten(@canon.canon_hnf(@core.mat_from_rows([[-6, -9]]))),
    @canon.flatten(@canon.canon_hnf(d)),
  )
  // 同一個秩 2 格的不同生成集
  let e1 = @core.mat_from_rows([[2, 0], [0, 3]])
  let e2 = @core.mat_from_rows([[2, 0], [2, 3]])
  assert_eq(
    @canon.flatten(@canon.canon_hnf(e1)),
    @canon.flatten(@canon.canon_hnf(e2)),
  )
  // 冪等
  assert_eq(
    @canon.flatten(@canon.canon_hnf(@canon.canon_hnf(b))),
    @canon.flatten(@canon.canon_hnf(b)),
  )
}

///|
/// [T-Canon-Conj] 相似規範形：M₂(F_q) 的相似類數 = q² + q（q = 2 → 6、q = 3 → 12）。
///   這條把規範形的「完備性」變成一個**可預測的整數**。
test "conjugacy canonical form: class counts match q^2+q" {
  assert_eq(@canon.conjugacy_class_count(2, 2), 6)
  assert_eq(@canon.conjugacy_class_count(2, 3), 12)
  // 冪等 + 不變性：A 與 PAP⁻¹ 同 canon
  let a = @core.mat_from_rows([[0, 1], [1, 1]])
  let p = @core.mat_from_rows([[1, 1], [0, 1]])
  let inv = @core.mat_from_rows([[1, 1], [0, 1]]) // 在 F_2 上自己就是反矩陣
  let conj = @core.mat_mul(@core.mat_mul(p, a, 2), inv, 2)
  assert_eq(@canon.canon_conj(a, 2), @canon.canon_conj(conj, 2))
  // 軌道分割檢核：Σ_{類} |類| = 16（每個矩陣恰屬於一個相似類）
  let seen : Array[Array[Int32]] = []
  let mut total = 0
  for code = 0; code < 16; code = code + 1 {
    let m = @core.mat_make(2, 2, 0)
    let mut c = code
    for i = 0; i < 2; i = i + 1 {
      for j = 0; j < 2; j = j + 1 {
        m.data[i * 2 + j] = c % 2
        c = c / 2
      }
    }
    let k = @canon.canon_conj(m, 2)
    let mut dup = false
    for x in seen {
      if x == k {
        dup = true
      }
    }
    if !dup {
      seen.push(k)
      total = total + @canon.orbit_size_conj(m, 2)
    }
  }
  assert_eq(total, 16)
  assert_eq(seen.length(), 6)
}

///|
/// [T-Canon-Conj-Poly] canon_conj **嚴格細於**特徵多項式：
///   diag(1,1) 與 Jordan 塊在 F_3 上同特徵多項式 (x−1)² 但不同 canon。
test "conjugacy canonical form strictly refines the characteristic polynomial" {
  let diag = @core.mat_from_rows([[1, 0], [0, 1]])
  let jord = @core.mat_from_rows([[1, 1], [0, 1]])
  assert_eq(@spectral.char_poly(diag, 3), @spectral.char_poly(jord, 3))
  assert_eq(@canon.canon_conj(diag, 3) == @canon.canon_conj(jord, 3), false)
}

///|
/// [T-Canon-Graph] 圖規範形完備於同構；且它**細於**線性相似規範形
///   （換標號是置換相似，置換 ⊂ GL）。
test "graph canonical form refines similarity canonical form" {
  // 同一張圖的兩個標號
  let g1 = graph_from_edges(4, [(0, 1), (1, 2), (2, 3)], 2)
  let g2 = graph_from_edges(4, [(2, 3), (3, 0), (0, 1)], 2) // 旋轉一格
  assert_eq(@canon.canon_graph(g1), @canon.canon_graph(g2))
  // 不同構：路徑 P₄ vs 星 K_{1,3}
  let star = graph_from_edges(4, [(0, 1), (0, 2), (0, 3)], 2)
  assert_eq(@canon.canon_graph(g1) == @canon.canon_graph(star), false)
  // 細化：canon_graph 相同 ⟹ canon_conj 相同（n = 3 全枚舉）
  let mut ok = true
  let mats : Array[@core.Mat] = []
  for code = 0; code < 8; code = code + 1 {
    let m = @core.mat_make(3, 3, 0)
    let edges : Array[(Int32, Int32)] = []
    for j = 0; j < 3; j = j + 1 {
      if (code >> j) % 2 == 1 {
        edges.push(
          if j == 0 {
            (0, 1)
          } else if j == 1 {
            (1, 2)
          } else {
            (0, 2)
          },
        )
      }
    }
    let g = graph_from_edges(3, edges, 2)
    let _ = m
    mats.push(g)
  }
  for i = 0; i < mats.length(); i = i + 1 {
    for j = 0; j < mats.length(); j = j + 1 {
      if @canon.canon_graph(mats[i]) == @canon.canon_graph(mats[j]) {
        if @canon.canon_conj(mats[i], 2) != @canon.canon_conj(mats[j], 2) {
          ok = false
        }
      }
    }
  }
  assert_eq(ok, true)
}

///|
/// [T-Canon-Metric] 度量空間的等距規範形。
test "metric canonical form is complete for isometry" {
  // 四個點在直線上：距離 = |i−j|
  let line = @core.mat_from_rows([
    [0, 1, 2, 3],
    [1, 0, 1, 2],
    [2, 1, 0, 1],
    [3, 2, 1, 0],
  ])
  // 重標號：把點 1 與 2 交換
  let perm : Array[Int32] = [0, 2, 1, 3]
  let relabeled = @canon.perm_conj_mat(line, perm)
  assert_eq(@canon.canon_metric(line), @canon.canon_metric(relabeled))
  // 星形度量（中心到三葉距離 1、葉間 2）與直線度量不同距
  let star = @core.mat_from_rows([
    [0, 1, 1, 1],
    [1, 0, 2, 2],
    [1, 2, 0, 2],
    [1, 2, 2, 0],
  ])
  assert_eq(@canon.canon_metric(line) == @canon.canon_metric(star), false)
}

///|
/// [T-Canon-T3] 2×2×2 張量（F_2，共 256 個）在 S_3 腿置換下的軌道數：
///   由 canon 數出的軌道數必須等於 Burnside 的 (1/6)Σ|Fix|。
test "tensor canonical form: orbit count equals Burnside" {
  let d = 2
  let total = 256
  // Burnside：單位 256、三個交換各 fix 多少、兩個三循環各 fix 多少
  let mut fix_sum = 0
  let perms3 : Array[Array[Int32]] = [
    [0, 1, 2],
    [0, 2, 1],
    [1, 0, 2],
    [1, 2, 0],
    [2, 0, 1],
    [2, 1, 0],
  ]
  let seen : Array[Array[Int32]] = []
  for code = 0; code < total; code = code + 1 {
    let flat : Array[Int32] = []
    let mut c = code
    for i = 0; i < 8; i = i + 1 {
      flat.push(c % 2)
      c = c / 2
    }
    let key = @canon.canon_t3(flat, d)
    let mut dup = false
    for x in seen {
      if x == key {
        dup = true
      }
    }
    if !dup {
      seen.push(key)
    }
    // 這個張量是否被該置換固定
    for pm in perms3 {
      let out : Array[Int32] = Array::make(8, 0)
      for a = 0; a < d; a = a + 1 {
        for b = 0; b < d; b = b + 1 {
          for q = 0; q < d; q = q + 1 {
            let src = (
                (if pm[0] == 0 { a } else if pm[0] == 1 { b } else { q }) * d +
                (if pm[1] == 0 { a } else if pm[1] == 1 { b } else { q })
              ) *
              d +
              (if pm[2] == 0 { a } else if pm[2] == 1 { b } else { q })
            out[(a * d + b) * d + q] = flat[src]
          }
        }
      }
      if out == flat {
        fix_sum = fix_sum + 1
      }
    }
  }
  assert_eq(seen.length(), fix_sum / 6)
}

///|
/// [T-Canon-Dihedral] 非交叉結構的二面體規範形 + Burnside 交叉驗證。
test "dihedral canonical form: orbits match Burnside" {
  // 5 邊形：所有單邊與所有「兩條邊」的組合（族在 D_5 下封閉 —— Burnside 才適用）
  let singles : Array[Array[@nc.Chord]] = []
  for a = 0; a < 5; a = a + 1 {
    for b = a + 1; b < 5; b = b + 1 {
      singles.push([@nc.chord(a, b)])
    }
  }
  let sets : Array[Array[@nc.Chord]] = []
  for s in singles {
    sets.push(s)
  }
  for i = 0; i < singles.length(); i = i + 1 {
    for j = i + 1; j < singles.length(); j = j + 1 {
      let e1 = singles[i][0]
      let e2 = singles[j][0]
      if e1.a != e2.a && e1.a != e2.b && e1.b != e2.a && e1.b != e2.b {
        sets.push([e1, e2])
      }
    }
  }
  let (orbits, burnside) = @canon.dihedral_orbits(5, sets)
  assert_eq(orbits, burnside)
  // 邊與邊同軌道、對角線與對角線同軌道，但邊 ≠ 對角線
  assert_eq(
    @canon.canon_dihedral(5, [@nc.chord(0, 1)]),
    @canon.canon_dihedral(5, [@nc.chord(3, 4)]),
  )
  assert_eq(
    @canon.canon_dihedral(5, [@nc.chord(0, 2)]),
    @canon.canon_dihedral(5, [@nc.chord(1, 3)]),
  )
  assert_eq(
    @canon.canon_dihedral(5, [@nc.chord(0, 1)]) ==
    @canon.canon_dihedral(5, [@nc.chord(0, 2)]),
    false,
  )
}

///|
/// [T-Canon-Cocycle] 上圈規範形：G = (Z/2)²、ℓ = 2 時
///   不同的 canon 個數 = |H²| = 2^{k(k+1)/2} = 2³ = 8。
test "cocycle canonical form: distinct classes equal |H^2|" {
  let g = @twist.grp([2, 2])
  let ell = 2
  let nv = @twist.var_count(g)
  let h2 = @twist.h2_dim(g, ell)
  assert_eq(h2, 3) // k(k+1)/2 = 3
  let seen : Array[Array[Int32]] = []
  let total = @core.int_pow(ell, nv)
  for code = 0; code < total; code = code + 1 {
    let v : Array[Int32] = []
    let mut c = code
    for i = 0; i < nv; i = i + 1 {
      v.push(c % ell)
      c = c / ell
    }
    if @canon.is_cocycle(g, ell, v) {
      let k = @canon.canon_cocycle(g, ell, v)
      let mut dup = false
      for x in seen {
        if x == k {
          dup = true
        }
      }
      if !dup {
        seen.push(k)
      }
    }
  }
  // |H²| = 2^{h²}
  assert_eq(seen.length(), @core.int_pow(2, h2))
}

///|
/// [T-Canon-Poset] site 規範形：換標號不變、不同構者不同。
test "site canonical form is complete for poset isomorphism" {
  let leq : Array[Array[Bool]] = [
    [true, true, true, true],
    [false, true, false, true],
    [false, false, true, true],
    [false, false, false, true],
  ]
  let s = @grotop.site_new(leq, 2)
  // 換標號：交換 1 與 2
  let perm : Array[Int32] = [0, 2, 1, 3]
  let leq2 : Array[Array[Bool]] = Array::makei(4, _ => Array::make(4, false))
  for i = 0; i < 4; i = i + 1 {
    for j = 0; j < 4; j = j + 1 {
      leq2[perm[i]][perm[j]] = leq[i][j]
    }
  }
  let s2 = @grotop.site_new(leq2, 2)
  assert_eq(@canon.canon_poset(s), @canon.canon_poset(s2))
  // 不同構：全序鏈 0<1<2<3 vs 上述 V 形
  let chain : Array[Array[Bool]] = Array::makei(4, i => {
    Array::makei(4, j => i <= j)
  })
  let s3 = @grotop.site_new(chain, 2)
  assert_eq(@canon.canon_poset(s) == @canon.canon_poset(s3), false)
}

///|
/// [T-Canon-Cx] 胞腔複形規範形：重排胞腔不變；有撓率者不同。
test "cell complex canonical form: reordering invariance and torsion" {
  let lens = @cellcx.cx_lens(5, 1, 7)
  let c0 = @canon.canon_cx(lens)
  // 對每個非零邊界做「換基」：把某一列（胞腔基向量）乘 −1（整數么模 ⟹ Smith 不變）
  let flipped = @cellcx.cx_lens(5, 1, 7)
  for k = 0; k < flipped.bnd.length(); k = k + 1 {
    let m = flipped.bnd[k]
    if m.rows > 0 {
      for j = 0; j < m.cols; j = j + 1 {
        m.data[0 * m.cols + j] = -m.data[0 * m.cols + j]
      }
    }
  }
  assert_eq(@canon.canon_cx(flipped), c0)
  // 球面 S²（無撓率）與透鏡 L(5,1)（有 Z/5 撓率）不同 canon
  assert_eq(@canon.canon_cx(@cellcx.cx_sphere(2, 7)) == c0, false)
  // L(5,1) 與 L(7,1) 的撓率不同
  assert_eq(c0 == @canon.canon_cx(@cellcx.cx_lens(7, 1, 11)), false)
}

///|
/// [T-Canon-Page] 譜序列頁的規範形在「逐格換基」下不變（RREF 是行空間的完全不變量）。
test "page canonical form is invariant under change of basis" {
  let pg = @ss.page_new(2, 0, 0, 3, 3, 7)
  @ss.page_setdim(pg, 0, 1, 2) // 源 2 維
  @ss.page_setdim(pg, 2, 0, 2) // 靶 2 維
  @ss.page_setd(pg, 0, 1, @core.mat_from_rows([[1, 2], [0, 3]]))
  let c0 = @canon.canon_page(pg)
  // 換基：d ↦ Q d P⁻¹
  let q = shear(2, 7)
  let p = @core.mat_from_rows([[1, 0], [2, 1]])
  match @spectral.mat_inverse(p, 7) {
    Some(pinv) => {
      let d = @core.mat_mul(
        @core.mat_mul(q, @core.mat_from_rows([[1, 2], [0, 3]]), 7),
        pinv,
        7,
      )
      @ss.page_setd(pg, 0, 1, d)
      assert_eq(@canon.canon_page(pg), c0)
    }
    None => fail("反矩陣不存在（不應該）")
  }
}

///|
/// [T-Canon-AlgProfile] 分次代數的秩剖面在逐度換基下不變。
test "graded algebra rank profile is basis independent" {
  let a = @ahss.alg_wedge([1, 1, 1], 2)
  // 逐度換基 P_0..P_3：剪切（det = 1）與置換（det = ±1），皆為么模 ⟹ 可逆
  let ps : Array[@core.Mat] = []
  for k = 0; k <= 3; k = k + 1 {
    let n = a.dims[k]
    let m = eye(n)
    if n >= 2 {
      m.data[0 * n + 1] = 1 // I + E₀₁
    }
    if n == 3 {
      // 再乘一個 3-循環置換（det = +1）
      let perm = eye(3)
      perm.data[0 * 3 + 0] = 0
      perm.data[1 * 3 + 1] = 0
      perm.data[2 * 3 + 2] = 0
      perm.data[0 * 3 + 1] = 1
      perm.data[1 * 3 + 2] = 1
      perm.data[2 * 3 + 0] = 1
      let prod = @core.mat_mul(m, perm, 2)
      ps.push(prod)
    } else {
      ps.push(m)
    }
  }
  let prof0 = @canon.canon_alg_profile(a)
  let b = @ahss.alg_skeleton(a.dims, 2)
  for i = 0; i <= 3; i = i + 1 {
    for j = 0; i + j <= 3; j = j + 1 {
      let c = @ahss.alg_get_cup(a, i, j)
      let newc = @core.mat_mul(
        @core.mat_mul(ps[i + j], c, 2),
        @ahss.kron(ps[i], ps[j], 2),
        2,
      )
      @ahss.alg_set_cup(b, i, j, newc)
    }
  }
  assert_eq(@core.det_mod(ps[2], @core.mk_field(2)), 1)
  // 部分 P_k 可能意外不可逆（例如 n=1 時 m=[1]，可逆）；逐一檢查
  assert_eq(@canon.canon_alg_profile(b), prof0)
}

///|
/// [T-Canon-Chain] 凝聚鏈的規範形在逐層換基下不變，且決定逆極限維數。
test "condensed chain canonical form" {
  let pr = @condensed.prof_zp(3, 2)
  let c = @condensed.chain_free(pr)
  let c0 = @canon.canon_chain(c)
  // 逐層換基：trans ↦ Q · trans · P⁻¹（Q: 2×2、P: 4×4，皆么模 ⟹ Smith 不變）
  let q = shear(2, 2)
  let p = eye(4)
  p.data[0 * 4 + 1] = 1 // I + E₀₁（4×4 剪切）
  match @spectral.mat_inverse(p, 2) {
    Some(pinv) => {
      let d = @core.mat_mul(@core.mat_mul(q, c.trans[0], 2), pinv, 2)
      let c2 = @condensed.chain_free(pr)
      c2.trans[0] = d
      assert_eq(@canon.canon_chain(c2), c0)
    }
    None => fail("反矩陣不存在（不應該）")
  }
  // 層級 0 是 Z/2（2 個點）⟹ 逆極限（常數函數）維數 = 2
  assert_eq(@condensed.chain_lim_dim(c), 2)
}

///|
/// [T-Canon-Gauge] 曲率是規範不變量（故 canon 在規範變換下不變）；
///   並給出**不完備性見證**：環面上「平坦但 holonomy ≠ 0」的場與零場同曲率，
///   卻不在零場的規範軌道上。
test "gauge canonical form: curvature invariant, and incomplete on a torus" {
  let l = @gauge.mk_lattice(3, 2)
  let sites = @gauge.lat_sites(l)
  let u = Array::make(2 * sites, 0)
  let lam = Array::make(sites, 1)
  let u2 = @gauge.gauge_transform(l, u, lam)
  assert_eq(@canon.canon_gauge(l, u), @canon.canon_gauge(l, u2))
  // 平坦但非純規範：所有 x-邊取 1、y-邊取 0 ⟹ 每個 plaquette 的曲率 = 0
  let flat = Array::make(2 * sites, 0)
  for y = 0; y < 3; y = y + 1 {
    for x = 0; x < 3; x = x + 1 {
      flat[2 * (x * 3 + y)] = 1
    }
  }
  let zero_curv = @canon.canon_gauge(l, flat)
  let mut all_zero = true
  for v in zero_curv {
    if v != 0 {
      all_zero = false
    }
  }
  assert_eq(all_zero, true)
  assert_eq(@canon.canon_gauge(l, u), zero_curv) // 曲率相同
  // 但 flat 不在零場的規範軌道上（窮舉全部 λ ∈ (Z/2)^9）
  let mut reachable = false
  for code = 0; code < 512; code = code + 1 {
    let lam2 : Array[Int32] = []
    let mut c = code
    for k = 0; k < sites; k = k + 1 {
      lam2.push(c % 2)
      c = c / 2
    }
    let moved = @gauge.gauge_transform(l, u, lam2)
    if moved == flat {
      reachable = true
    }
  }
  // 註：零場在所有規範變換下都是零場，故 flat（非零）不可能被達到
  assert_eq(reachable, false)
}

///|
/// [T-Canon-HyperIso] 超結構的同構規範形：換標號不變、不同構者不同。
test "hyperstructure canonical form" {
  // Z/4 的加法表（含 0..3）vs Z/2×Z/2
  let z4 = @hyper.hyper_from(4, fn(a, b, c) { (a + b) % 4 == c })
  let v4 = @hyper.hyper_from(4, fn(a, b, c) {
    let x = (a % 2 + b % 2) % 2
    let y = (a / 2 + b / 2) % 2
    2 * y + x == c
  })
  assert_eq(@canon.canon_hyper_iso(z4) == @canon.canon_hyper_iso(v4), false)
  // 用**非自同構**的置換 σ(i) = i+1 造同構副本：a·b = σ(σ⁻¹(a) + σ⁻¹(b))
  // （若用自同構，交換群的乘法表其實逐項不變 —— 這條測試特別避開那個退化）
  let relabel : @hyper.Hyper = @hyper.hyper_from(4, fn(a, b, c) {
    let inv : Array[Int32] = [3, 0, 1, 2]
    let sig : Array[Int32] = [1, 2, 3, 0]
    sig[(inv[a] + inv[b]) % 4] == c
  })
  // 同構 ⟹ 同構規範形相同
  assert_eq(@canon.canon_hyper_iso(z4), @canon.canon_hyper_iso(relabel))
  // 精確編碼（不除標號）則會不同 —— 兩者都如實保留
  assert_eq(@canon.canon_hyper(z4) == @canon.canon_hyper(relabel), false)
}

///|
/// [T-Canon-Records] 記錄集合的規範形：次序與重複不影響，內容不同則不同。
test "relation records canonical form" {
  let r1 = @relations.rec(2, 5, 7, true)
  let r2 = @relations.rec(1, 3, 3, false)
  let a = @canon.canon_records([r1, r2])
  let b = @canon.canon_records([r2, r1, r1])
  assert_eq(a, b)
  let c = @canon.canon_records([@relations.rec(2, 5, 7, false)])
  assert_eq(a == c, false)
}

///|
/// [T-Canon-Tor] Tor 表的規範形在截斷提高時穩定（低度數不變）。
test "Tor canonical form: truncation stability" {
  let small = @canon.canon_tor(@dtensor.poly_alg(2, 4), 2, 4)
  let big = @canon.canon_tor(@dtensor.poly_alg(2, 6), 2, 4)
  assert_eq(small, big)
  let other = @canon.canon_tor(@dtensor.poly_alg(3, 4), 2, 4)
  assert_eq(small == other, false)
}
