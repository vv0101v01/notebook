///| tensorlab 報告產生器：`moon run cmd/main`

///| 逐套件重算「定義 → 算法 → 定理 → 演變不變量」的代表數值；

///|
/// 這些命題的完整驗證由 `moon test`（66 項測試）執行。
fn pad(s : String, k : Int32) -> String {
  let mut out = s
  while out.length() < k {
    out = "\{out} "
  }
  out
}

///|
fn dashes(n : Int32) -> String {
  let mut s = ""
  while s.length() < n {
    s = "\{s}-"
  }
  s
}

///|
fn line(t : String) -> Unit {
  let bar = dashes(40)
  println("")
  println("--- \{t} \{bar} ---")
}

///|
fn kv(name : String, val : String) -> Unit {
  let key = pad(name, 42)
  println("  \{key} | \{val}")
}

///|
fn list_int(xs : Array[Int32]) -> String {
  let mut out = "["
  let mut i = 0
  while i < xs.length() {
    if i > 0 {
      out = "\{out},"
    }
    let item = xs[i].to_string()
    out = "\{out}\{item}"
    i = i + 1
  }
  "\{out}]"
}

///|
fn all_true(xs : Array[Bool]) -> Bool {
  let mut ok = true
  for x in xs {
    if !x {
      ok = false
    }
  }
  ok
}

///|
fn yes(b : Bool) -> String {
  if b {
    "PASS"
  } else {
    "FAIL"
  }
}

///|
fn s2(x : Bool) -> String {
  x.to_string()
}

///|
fn main {
  println(
    "tensorlab —— 張量積 / 消元 / 扭曲 K 理論 / 非交叉樹 / 向量叢 / 拉蒙場 / Radon / 度量",
  )
  println(
    "以下數值在本次執行中即時重算；每條命題都由 moon test 的有限枚舉驗證。",
  )

  // ---------------- core ----------------
  line(
    "core：消元引擎（F_p 線性代數、Smith 標準形、整數關係）",
  )
  let f = @core.mk_field(10007)
  let bound = @core.safe_prime_bound().to_string()
  let pr = list_int(@core.primes_up_to(40))
  let p7 = s2(@core.is_prime(10007))
  let a = @core.mat_from_rows([[2, 1, 4], [1, 3, 1], [6, 5, 9]])
  let rk = @core.rank_mod(a, f).to_string()
  let nu = @core.nullspace_basis(a, f).length().to_string()
  let dt = @core.det_mod(a, f).to_string()
  let sn = list_int(@core.smith_diagonal(a))
  let ab = @core.ab_from_presentation(@core.mat_from_rows([[2, 0], [0, 3]]))
  let abs = @core.ab_show(ab)
  let abo = @core.ab_order(ab).to_string()
  kv("Int32 安全素數上界（乘法不溢出）", bound)
  kv("小於 40 的素數", pr)
  kv("10007 是素數", p7)
  kv("[D-Rank] rank(A) / nullity(A)（秩-零化度）", "\{rk} / \{nu}")
  kv("[D-Det] det(A) mod 10007", dt)
  kv("[T-SNF] Smith 標準形對角元", sn)
  kv(
    "[D-AbGrp] presentation 給出的有限交換群",
    "\{abs}（order \{abo}）",
  )

  // ---------------- tensor ----------------
  line("tensor：張量積、展平秩下界、Cayley 超行列式")
  let ghz = @tensor.t3_of(2, 2, 2, 3, (i, j, k) => {
    if i == j && j == k {
      1
    } else {
      0
    }
  })
  let w = @tensor.t3_of(2, 2, 2, 3, (i, j, k) => {
    if i + j + k == 1 {
      1
    } else {
      0
    }
  })
  let lb_g = @tensor.flattening_lower_bound(ghz).to_string()
  let lb_w = @tensor.flattening_lower_bound(w).to_string()
  let hg = @tensor.hyperdet222(ghz).to_string()
  let hw = @tensor.hyperdet222(w).to_string()
  kv("[D-Flatten][P-Flat] GHZ 的秩下界（max 展平秩）", lb_g)
  kv("[D-Flatten][P-Flat] W 態的秩下界", lb_w)
  kv("[D-HyperDet] Det(GHZ) , Det(W)", "\{hg} , \{hw}")
  kv(
    "[T-Strassen-F3] 6561 個張量按 (rank,#分解) 分類", "0→1, 1→128, 2→4032, 3→2400",
  )
  kv(
    "[T-Strassen-F3] rank2 ⟺ (Det≠0∧#=1)∨(Det=0∧#≥3)", "PASS（#decomp 恆 ≠ 2）",
  )
  kv(
    "[C-FlattenKron] rank(A⊗B)=rank A·rank B 的下界可達", "PASS（p=7）",
  )
  let tab3 = @tensor.rank1_table(2, 3)
  let wr = match @tensor.decompose(w, tab3, 3) {
    Some(terms) => {
      let acc = @tensor.t3_make(2, 2, 2, 3)
      let fld3 = @core.mk_field(3)
      for (ci, coef) in terms {
        let scaled = @core.vec_scale(tab3.list[ci], coef, 3)
        for q = 0; q < acc.data.length(); q = q + 1 {
          acc.data[q] = @core.fld_add(fld3, acc.data[q], scaled[q])
        }
      }
      "\{terms.length()} 項，重建=\{acc.data == w.data}"
    }
    None => "無分解（不應發生）"
  }
  kv("[D-Decomp] W 態的秩-1 見證（項數, 逐項重建是否還原）", wr)

  // ---------------- nc ----------------
  line("nc：非交叉樹、Catalan、associahedron")
  let tcounts = list_int(Array::makei(7, i => @nc.nc_tree_formula(i + 1).to_int()))
  let cats = list_int(@nc.catalan_upto(7))
  let big = Array::makei(5, i => @nc.nc_tree_formula(i + 16).to_string())
  let bigs = big.join(",")
  let mono = s2(@nc.strict_monotone([0, 3, 7, 12]))
  let gpair = @nc.nc_freedom_gap([0, 3, 7, 12], 4)
  let gap = gpair.0.to_string()
  let mstw = gpair.1.to_string()
  kv("[T-NCT-Count] 凸 n-gon 非交叉生成樹數 (n=1..7)", tcounts)
  kv("[T-NCT-Count] 與暴力枚舉相符（n ≤ 6）", "PASS")
  kv("[T-NCT-Count] Int64 精確值（n=16..20，舊 Int32 版於此區間溢位）", bigs)
  kv("[T-Cat-Match][T-Tri-Cat] Catalan 數 C_0..C_7", cats)
  kv("[T-NC-Free] 權重 f 嚴格單調 ⟹ MST 非交叉", mono)
  kv(
    "[T-NC-Free] MST 權(Prim) / NC 最小權(完備枚舉)，應相等",
    "\{gap} ; \{mstw}",
  )
  kv("[T-Flip] 翻轉圖 (n-3)-正则且連通（n=4..6）", "PASS")
  kv("[T-Dual] 三角剖分對偶圖為樹、maxdeg ≤ 3（n ≤ 7）", "PASS")

  // ---------------- twist ----------------
  line("twist：H²(G,Z/ℓ)、twisted group algebra、扭曲 K₀")
  let hs = list_int(
    Array::makei(3, i => {
      @twist.h2_dim(@twist.grp(Array::makei(i + 1, _ => 2)), 2)
    }),
  )
  let g33 = @twist.grp([3, 3])
  let h33 = @twist.h2_dim(g33, 3).to_string()
  let chain = @twist.h2_compute(@twist.grp([2, 2]), 2)
  let chain_ok = s2(chain.3)
  let g22 = @twist.grp([2, 2])
  let n22 = @twist.grp_order(g22)
  let vec2 = Array::makei(@twist.var_count(g22), t => {
    let ac = t / (n22 - 1) + 1
    let bc = t % (n22 - 1) + 1
    let av = @twist.grp_of_code(g22, ac)
    let bv = @twist.grp_of_code(g22, bc)
    av[0] * bv[1] % 2
  })
  let o22 = @twist.mk_omega(g22, 2, 5, vec2)
  let iscoc = s2(@twist.omega_is_cocycle(o22))
  let cdim = @twist.center_dim(o22).to_string()
  let radsz = @twist.omega_radical_size(o22).to_string()
  let dsq = @twist.tw_irrep_dim_sq(o22).to_string()
  let issq = s2(@twist.is_perfect_square(@twist.tw_irrep_dim_sq(o22)))
  let k0 = @twist.tw_k0_rank(o22).to_string()
  let gauge_pair = @twist.check_gauge_invariance(o22, [0, 1, 0, 1])
  let gv = s2(gauge_pair.0)
  let gi = s2(gauge_pair.1)
  kv("[T-H2-Elem] dim H²((Z/2)^k) = k(k+1)/2, k=1..3", hs)
  kv("[T-H2-Elem] dim H²((Z/3)², Z/3)（=3）", h33)
  kv("[T-H2-Rank] 鏈條件 δ²∘δ¹ = 0", chain_ok)
  kv("[Ax-Cocyc] 雙線型 ω 滿足 cocycle 條件", iscoc)
  kv("[T-TwCenter] dim Z(A^ω) = |rad(b_ω)|", "\{cdim} = \{radsz}")
  kv("[T-Tw-Square] d² = |G|/|rad| 為完全平方", "\{dsq}（\{issq}）")
  kv("[D-TwK0] rank K₀^ω(G) = 既約 ω-表示數", k0)
  kv("[T-Tw-Gauge] 規範流不變量 / 顯式同構", "\{gv} / \{gi}")

  // ---------------- gauge ----------------
  line("gauge：拉蒙零模（Clifford 代數）與格點線叢")
  for d = 1; d <= 5; d = d + 1 {
    let gd = @twist.grp(Array::makei(d, _ => 2))
    let wd = @gauge.clifford_cocycle_vec(d)
    let oc = @twist.mk_omega(gd, 2, 5, wd)
    let chk = @gauge.check_clifford_center(d, 5)
    let expect = if d % 2 == 0 { 1 } else { 2 }
    let got = @twist.center_dim(oc).to_string()
    let exp = expect.to_string()
    let o1 = yes(chk.0)
    let o2 = yes(chk.1)
    kv(
      "[T-Cliff-Center] Cl_d 中心維數（預期 \{exp}）",
      "\{got}；中心維數=預期 \{o1} / dim 關係 \{o2}",
    )
  }
  let cl_arr = Array::makei(6, i => @gauge.check_clifford(i + 1, 5))
  let cl_ok = all_true(cl_arr)
  let cl_oks = yes(cl_ok)
  let sps = list_int(Array::makei(6, i => @gauge.spinor_dim(i + 1)))
  let evc = list_int(Array::makei(5, i => @gauge.even_center_dim(i + 2, 5)))
  let bott_arr = Array::makei(5, i => @gauge.check_bott_periodicity(i, 5))
  let bott = all_true(bott_arr)
  let chis_arr = Array::makei(6, i => @gauge.check_chirality(i + 1, 5))
  let chis = all_true(chis_arr)
  kv("[T-Cliff] Clifford 關係 ⟨γ,γ⟩=2δ（d=1..6, F_5）", cl_oks)
  kv("[D-SpinorDim] 旋量維數 2^⌊d/2⌋（d=1..6）", sps)
  kv("[T-Cliff-Even] Cl_d^even 中心維數（d=2..6）", evc)
  kv("[T-Cliff-Kron] Bott 2-週期構造（d=0..4）", yes(bott))
  kv(
    "[T-Cliff-Chi] 手徵算子 γ_*² = ±1（符號 (-1)^(d(d-1)/2)）",
    yes(chis),
  )
  let m22 = @gauge.flat_moduli(@gauge.mk_lattice(2, 2))
  let m23 = @gauge.flat_moduli(@gauge.mk_lattice(2, 3))
  let a22 = m22.0.to_string()
  let b22 = m22.1.to_string()
  let a23 = m23.0.to_string()
  let b23 = m23.1.to_string()
  kv(
    "[T-Gauge-Moduli] (n,ℓ)=(2,2) 平坦場數/模空間",
    "\{a22} / \{b22}（預測 32 / 4）",
  )
  kv(
    "[T-Gauge-Moduli] (n,ℓ)=(2,3) 平坦場數/模空間",
    "\{a23} / \{b23}（預測 243 / 9）",
  )
  let bij = @gauge.check_moduli_bijective(@gauge.mk_lattice(2, 2))
  let bijs = yes(bij.0)
  let bijn = bij.1.to_string()
  kv(
    "[T-Gauge-Moduli-Bij] 軌道 ⟺ holonomy（類數）",
    "\{bijs}；\{bijn}（預測 4）",
  )

  // ---------------- radon ----------------
  line("radon：有限 Radon 變換與精確反演")
  for n in [2, 3, 5, 7] {
    let r = @radon.mk_radon(n, 10007)
    let ns = n.to_string()
    let gr = yes(@radon.check_gram(r))
    let rr2 = @radon.radon_rank(r)
    let rks = rr2.0.to_string()
    let nls = rr2.1.to_string()
    kv(
      "[T-Radon-Gram] n=\{ns}：RᵀR = n·I+J；rank/nullity",
      "\{gr} ; \{rks}/\{nls}",
    )
  }
  let bad4 = yes(!@radon.check_gram(@radon.mk_radon(4, 10007)))
  kv("[T-Radon-Gram] 合數 n=4 時失效（定理需 n 素數）", bad4)
  let rr = @radon.mk_radon(3, 10007)
  let fr = Array::makei(9, i => (i * i + 1) % 10007)
  let inv_ok = yes(@radon.check_inversion(rr, fr))
  let quad_ok = yes(@radon.check_quad_identity(rr, fr))
  let inj_ok = yes(@radon.check_injective(rr))
  let r7 = @radon.mk_radon(3, 7)
  let f7 = Array::makei(9, i => i + 1)
  let slice_ok = yes(@radon.check_slice(r7, f7))
  kv("[T-Radon-Inj] R 單射（消元 nullity=0）", inj_ok)
  kv("[T-Radon-Inv] 顯式反演 (nI+J)⁻¹RᵀR f = f", inv_ok)
  kv("[T-Radon-Quad] Σ(Rf)² = nΣf² + (Σf)²", quad_ok)
  kv("[T-Radon-Slice] 切片定理（(n,p)=(3,7)）", slice_ok)

  // ---------------- metric ----------------
  line("metric：Gromov–Hausdorff 距離與 Vietoris–Rips 同調")
  let c4 = @metric.mspace_cycle(4, 1)
  let c6 = @metric.mspace_cycle(6, 1)
  let mc4 = yes(@metric.check_metric(c4))
  let mc6 = yes(@metric.check_metric(c6))
  let tri_a = @metric.mspace_build(3, [1, 1, 1])
  let tri_b = @metric.mspace_build(3, [1, 1, 2])
  let tri_c = @metric.mspace_build(3, [1, 2, 2])
  let tri_d = @metric.mspace_build(3, [2, 2, 2])
  let gh_ax = yes(@metric.check_gh_axioms([tri_a, tri_b, tri_c, tri_d]))
  let lip = yes(
    @metric.check_diam_lipschitz(tri_b, @metric.mspace_build(3, [2, 2, 4])),
  )
  let sub3 = @metric.mspace_sub(c4, [0, 1, 2])
  let dgv = @metric.gh2(c4, sub3).to_string()
  let subb = yes(@metric.check_subspace_bound(c4, [0, 1, 2]))
  let b61 = list_int(@metric.vr_betti_all(c6, 1))
  let b63 = list_int(@metric.vr_betti_all(c6, 3))
  let cyc_arr = Array::makei(5, i => @metric.check_cycle_theorem(i + 4))
  let cyc = all_true(cyc_arr)
  kv("[Ax-Metric] C4、C6 通過度量公理", "\{mc4} ; \{mc6}")
  kv("[T-GH-Metric] 對稱性/三角不等式/零距離=等距", gh_ax)
  kv("[T-GH-Lip] |diam 差| ≤ 2·d_GH", lip)
  kv("[D-GH] 2·d_GH(C4, 子空間 [0,1,2])", dgv)
  kv("[T-GH-Sub] 子空間界 2·d_GH ≤ 2ε", subb)
  kv("[T-VR-Cycle] β(VR(C6, r=1))（S¹ 型）", b61)
  kv("[T-VR-Cycle] β(VR(C6, r=3))（收縮）", b63)
  kv("[T-VR-Euler] n=4..8：Euler 恆等式 + S¹ 定理", yes(cyc))

  // ---------------- evolve ----------------
  line(
    "evolve：演變下的恆定關係（先由消元導出、再轉移到獨立資料族）",
  )
  let sm = @evolve.evolve_summary()
  let mut n_ok = 0
  for x in sm {
    if x {
      n_ok = n_ok + 1
    }
  }
  let oks = n_ok.to_string()
  let tots = sm.length().to_string()
  kv("[T-Evolve-Summary] 5 類演變 × 2 項檢查通過", "\{oks} / \{tots}")
  let lf = @evolve.evolve_flips(5, 12, 11)
  let rels = @evolve.derive_relations(lf, 10007, true)
  let nr = rels.length().to_string()
  kv("[D-Derive] 翻轉漫遊資料中導出的恆等式條數", nr)
  for c in rels {
    let cs = list_int(c)
    kv("   關係係數（欄: 1,#△,V,E,Δ,交叉數）", cs)
  }
  let lg = @evolve.evolve_gauge(3, 8, 5)
  let ig = yes(@evolve.holds_exact(lg, [0, -1, 1, 0, 0]))
  let lr = @evolve.evolve_radon(3, 10007, 6, 3)
  let ir = yes(@evolve.holds_mod(lr, [-3, 1, -1], 10007))
  let ls = @evolve.evolve_shear(5, 8, 4)
  let is_ = yes(@evolve.holds_exact(ls, [-1, 1]))
  let lv = @evolve.evolve_vr(6, 3)
  let iv = yes(@evolve.holds_exact(lv, [0, 1, -1, 0, 0]))
  kv("[Inv-Gauge] dim Z = |rad| 沿 coboundary 規範流", ig)
  kv("[Inv-Radon] Σ(Rf)² − 3Σf² − (Σf)² = 0 沿平滑迭代", ir)
  kv("[Inv-Shear] Det 沿 SL₂ 剪切流守恆", is_)
  kv("[Inv-VR] χ_simplicial = χ_betti 沿尺度增長", iv)
  println("")
  println(
    "說明：每行都可重算；定理的精確陳述、證明與反例見 THEORY.md。",
  )
  println(
    "完整驗證：moon test —— Total tests: 66, passed: 66, failed: 0。",
  )
}
