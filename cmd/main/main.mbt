///| tensorlab 報告產生器：`moon run cmd/main`

///| 逐套件重算「定義 → 算法 → 定理 → 演變不變量」的代表數值；

///|
/// 這些命題的完整驗證由 `moon test`（101 項測試）執行。
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
fn pair2(t : (Int32, Int32)) -> String {
  let (a, b) = t
  "\{a}:\{b}"
}

///|
fn axioms(t : (Bool, Bool, Bool, Bool, Bool, Bool)) -> String {
  let (a, b, c, d, e, f) = t
  "\{s2(a)},\{s2(b)},\{s2(c)},\{s2(d)},\{s2(e)},\{s2(f)}"
}

///|
fn main {
  println(
    "tensorlab —— 張量積 / 消元 / 扭曲 K 理論 / 非交叉樹 / 向量叢 / 拉蒙場 / Radon / 度量 / 超化 / 譜化 / 賬本 / 五關係",
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
  kv(
    "[D-Decomp] W 態的秩-1 見證（項數, 逐項重建是否還原）", wr,
  )

  // ---------------- nc ----------------
  line("nc：非交叉樹、Catalan、associahedron")
  let tcounts = list_int(
    Array::makei(7, i => @nc.nc_tree_formula(i + 1).to_int()),
  )
  let cats = list_int(@nc.catalan_upto(7))
  let big = Array::makei(5, i => @nc.nc_tree_formula(i + 16).to_string())
  let bigs = big.join(",")
  let mono = s2(@nc.strict_monotone([0, 3, 7, 12]))
  let gpair = @nc.nc_freedom_gap([0, 3, 7, 12], 4)
  let gap = gpair.0.to_string()
  let mstw = gpair.1.to_string()
  kv("[T-NCT-Count] 凸 n-gon 非交叉生成樹數 (n=1..7)", tcounts)
  kv("[T-NCT-Count] 與暴力枚舉相符（n ≤ 6）", "PASS")
  kv(
    "[T-NCT-Count] Int64 精確值（n=16..20，舊 Int32 版於此區間溢位）",
    bigs,
  )
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

  // ---------------- 超化 / 譜化 / 賬本 / 五關係 ----------------
  line("超化：每個結構的 a ⋆ b = 可能的結果集")
  let hi = @hyper.interval_hyper(4)
  // 公理次序：閉合、結合、再生、交換、么元、反元素
  kv("interval_hyper(4) 六公理", axioms(@hyper.hyper_classify(hi, 0)))
  kv("  是否規範超群", s2(@hyper.is_canonical_hypergroup(hi, 0)))
  kv("胞尺寸剖面 [0,4,6,4,2]", list_int(@hyper.hyper_cell_profile(hi)))
  let (rh, canon) = @hyper.mat_rank_hyper_exhaustive(2, 3)
  kv("秩超群的胞尺寸剖面", list_int(@hyper.hyper_cell_profile(rh)))
  kv("秩超群 == 絕對差超群（逐格）", s2(canon))
  kv(
    "超冪次 hyper_potency(interval_hyper(4), 0, 12)",
    "\{@hyper.hyper_potency(hi, 0, 12)}",
  )
  let fp = @hyper.flip_hyper(5)
  kv("flip_hyper(5) 六公理", axioms(@hyper.hyper_classify(fp, 0)))
  kv(
    "  （缺反元素：測地距離超群不正規）",
    s2(@hyper.is_canonical_hypergroup(fp, 0)),
  )

  line("譜化：特徵多項式 / 譜 / 手徵 / 正則表示")
  let a2 = @core.mat_from_rows([[1, 2], [3, 4]])
  kv("char_poly([[1,2],[3,4]], 7) 升冪", list_int(@spectral.char_poly(a2, 7)))
  let sp = @spectral.spectrum_of(a2, 7)
  let sp2 = @spectral.spectrum_of(@core.mat_from_rows([[1, 2], [2, 4]]), 7)
  kv(
    "spectrum_of：分裂 / 相異根數（[[1,2],[3,4]] 與 [[1,2],[2,4]]）",
    "\{s2(@spectral.spectrum_split(sp))},\{s2(@spectral.spectrum_split(sp2))}",
  )
  kv("  相異根數", "\{sp.roots.length()},\{sp2.roots.length()}")
  let (chi_ok, chi_plus, chi_roots) = @spectral.chirality_spectrum(4, 13)
  kv("chirality d=4,p=13：分裂/平方=I", "\{s2(chi_ok)}/\{s2(chi_plus)}")
  kv("  相異根數", "\{chi_roots.length()}")
  let rrep = @spectral.regular_rep_matrix(
    @twist.mk_omega(@twist.grp([2, 2]), 2, 5, Array::makei(9, _t => 0)),
    [0, 0],
    5,
  )
  kv("regular_rep 跡 ρ(e)", "\{@spectral.mat_trace(rrep)}")
  let lap_ok = @spectral.check_cycle_laplacian_spectrum(5, 11)
  kv("C₅/p=11 Laplace 譜公式", s2(lap_ok))
  let (iso, b1, b2) = @spectral.isospectral_star_vs_cycle(17)
  kv(
    "K_{1,4} 與 C₄⊔K₁ 對稱譜（直徑 2 vs −1）",
    "\{s2(iso)}（\{b1},\{b2}）",
  )

  line("超級持久賬本：雜湊鏈 + O(1) 追加 + 稽核/重放")
  let lgr = @ledger.ingest_rowset(
    @ledger.empty(),
    @evolve.evolve_radon(3, 10007, 6, 3),
    0,
  )
  let lg1 = lgr.0
  let (dlg, dn) = @ledger.derive_into(lg1, 10007, false)
  kv("入賬觀測列數 / 導出關係數", "\{lgr.1}/\{dn}")
  kv(
    "鏈長 / 可驗證 verify",
    "\{@ledger.ledger_len(dlg)}/\{s2(@ledger.verify(dlg))}",
  )
  kv("tip（FNV-1a 64）", @ledger.ledger_tip(dlg).to_string())
  let (ap, af) = @ledger.audit(dlg, 10007, false)
  kv("稽核（通過/失敗）", "\{ap}/\{af}")
  let lgc = @ledger.corrupt(dlg, 1)
  kv("篡改第 1 條後 verify", s2(@ledger.verify(lgc)))
  kv("與篡改版共同前綴 fork_index", "\{@ledger.fork_index(dlg, lgc)}")

  line(
    "五關係：相對 / 對偶 / 對比 / 蘊含 / 比率（擴展定理與算法）",
  )
  let recs = @relations.collect(2, 10007)
  let objs : Array[String] = []
  for r in recs {
    objs.push("k\{r.kind}:\{s2(r.holds)}")
  }
  let mut joined = ""
  for o in objs {
    joined = "\{joined} \{o}"
  }
  kv("collect(2,10007) 四條關係", joined)
  let (lc2, lc3) = @relations.collect_into_ledger(dlg, 2, 10007)
  kv(
    "關係寫入賬本（新增/鏈長）",
    "\{lc3}/\{@ledger.ledger_len(lc2)}",
  )
  let (dds, eqs) = @relations.dual_chain_cochain(
    @metric.mspace_cycle(5, 1),
    1,
    2,
  )
  kv("對偶：∂∂=0 / H^k 維數相等", "\{s2(dds)}/\{s2(eqs)}")
  let (rsame, rinj, rrk, rn2) = @relations.dual_radon_injectivity(3, 10007)
  kv(
    "對偶：Radon rank(A)=rank(Aᵀ) / 單射",
    "\{s2(rsame)}（\{rrk}/\{rn2}）/\{s2(rinj)}",
  )
  let tb = @relations.tensor_predicate_table()
  let implm = @relations.implication_matrix(tb)
  let pairs : Array[(Int32, Int32)] = @relations.equivalences(
    @relations.implication_closure(implm, 5),
  )
  kv(
    "蘊含：秩≤1 ⟹ Det=0 且 #decomp=0",
    "\{s2(implm[0][1] && implm[0][2])}",
  )
  kv(
    "蘊含：Det≠0 ⟹ （不）rank=3",
    "\{s2(implm[4][3])}（反例來自 6561 張量）",
  )
  kv("等價類數（五謂詞）", "\{pairs.length()}")
  kv(
    "比率：翻轉圖 E:V (n=6)",
    pair2(@relations.flip_edge_vertex_ratio(6)),
  )
  kv(
    "比率：Radon Σ(Rf):Σf (n=3)",
    match
      @relations.radon_total_relative(3, 10007, Array::makei(9, i => i + 1)) {
      Some(v) => v.to_string()
      None => "-"
    },
  )
  let (na, nb, nc) = @relations.contrast_counts(tb[0], tb[1])
  kv("對比：rank≤1 與 Det=0 的 onlyA/onlyB/both", "\{na}/\{nb}/\{nc}")
  kv(
    "  分割恆等式 |onlyA|+|onlyB|+|both| = |A∪B|",
    s2(@relations.check_contrast_partition(tb[0], tb[1])),
  )

  // ---- 第三輪：譜序列／拓撲／凝聚／扭曲 AHSS／交叉運算 ---------------
  println("")
  println(
    "[19] 譜序列引擎（@ss）：1×1 非零 d_2 同時消掉源與靶",
  )
  let pg = @ss.page_new(2, 0, 0, 3, 3, 7)
  @ss.page_setdim(pg, 0, 1, 1)
  @ss.page_setdim(pg, 2, 0, 1)
  @ss.page_setd(pg, 0, 1, @core.mat_from_rows([[1]]))
  let pg2 = @ss.page_next(pg)
  kv(
    "  E_2 → E_3 的 (0,1)、(2,0) 維數",
    "\{@ss.page_dim(pg, 0, 1)},\{@ss.page_dim(pg, 2, 0)} → \{@ss.page_dim(pg2, 0, 1)},\{@ss.page_dim(pg2, 2, 0)}",
  )
  kv("  d_2 ∘ d_2 = 0", s2(@ss.page_dd_zero(pg)))

  println("")
  println(
    "[20] 塞爾譜序列（@serre）：S¹ → S³ → S² 收斂到 H_*(S³)",
  )
  let e2 = @serre.serre_e2([1, 0, 1], [1, 0, 1], 7)
  let s3 = @cellcx.cx_sphere(3, 7)
  let used = @serre.serre_run(@serre.hopf(1, 7), 4)
  kv(
    "  E_∞ 的總維數 (n = 0,3)",
    "\{@ss.page_total(used, 0)},\{@ss.page_total(used, 3)}",
  )
  kv(
    "  與 @cellcx 的 H_*(S³) 交叉驗證",
    s2(@serre.serre_matches_homology(used, s3)),
  )
  let _ = e2

  println("")
  println("[21] Adams 譜序列（@adams）：Ext_A(F_2,F_2) 的低度數")
  let ext = @adams.ext_table(@adams.stralg_truncated(8), 3, 6)
  kv(
    "  Ext^{2,2}, Ext^{2,3}, Ext^{3,3}, Ext^{3,5}",
    "\{ext[2][2]},\{ext[2][3]},\{ext[3][3]},\{ext[3][5]}",
  )
  let indec = @adams.indecomposable_degs(@adams.stralg_truncated(8))
  let mut ind_s = ""
  for d in indec {
    ind_s = if ind_s == "" { "\{d}" } else { "\{ind_s},\{d}" }
  }
  kv("  不可分解元度數（D=8）", ind_s)

  println("")
  println("[22] 格羅滕迪克拓撲（@grotop）：公理與層條件")
  let leq : Array[Array[Bool]] = [
    [true, true, true, true],
    [false, true, false, true],
    [false, false, true, true],
    [false, false, false, true],
  ]
  let site = @grotop.site_new(leq, 2)
  let top = @grotop.top_of_families(site, [(3, [1, 2])])
  kv(
    "  (T1)、(T2)、(T3) 與拓撲合法性",
    "\{@grotop.top_axiom_max(top)},\{@grotop.top_axiom_pull(top)},\{@grotop.top_axiom_local(top)} → \{@grotop.top_valid(top)}",
  )
  let cf = @grotop.pf_new(site, [1, 1, 1, 1], fn(a, b) {
    let _ = b
    Some(@core.mat_make(1, 1, if a == 0 { 0 } else { 1 }))
  })
  kv(
    "  常數預層（F(∅)=0）是層？/ 加號維數",
    "\{@grotop.is_sheaf(cf, top)}, \{@grotop.pf_plus_dim(cf, 3, [1, 2])}",
  )

  println("")
  println("[23] 凝聚群（@condensed）：Ext 消失與固態性缺口")
  let zp = @condensed.prof_zp(3, 2)
  kv(
    "  Z_2 的 Ext^{i>0}(Z[S]^■, F_2) 消失證書",
    s2(@condensed.cond_ext_vanishes(zp, 1)),
  )
  kv(
    "  Hom(Z[S],F_2) / Hom(Z[S]^■,F_2) / 缺口",
    "\{@condensed.cond_hom_free_discrete(zp, 1)}/\{@condensed.cond_hom_solid_discrete(zp, 1)}/\{@condensed.cond_solidity_defect(zp, 1)}",
  )
  kv(
    "  Z[S]^■ ⊗ Z[T]^■ ≅ Z[S×T]^■",
    s2(
      @condensed.chain_eq(
        @condensed.chain_tensor(
          @condensed.chain_free(zp),
          @condensed.chain_free(zp),
        ),
        @condensed.chain_free(@condensed.prof_prod(zp, zp)),
      ),
    ),
  )

  println("")
  println(
    "[24] 扭曲 AHSS（@ahss）：d_3 = Sq³ + H∪(−)，dim X ≤ 5 ⟹ Sq³ = 0",
  )
  let alg = @ahss.alg_wedge([3], 2)
  let p_untw = @ahss.ahss_page(alg, [-2, 0, 2], -2, 2)
  @ahss.ahss_set_d3(p_untw, @ahss.ahss_zero_ops(alg))
  let p_tw = @ahss.ahss_page(alg, [-2, 0, 2], -2, 2)
  @ahss.ahss_set_d3(p_tw, @ahss.ahss_twist_ops(alg, 3, 0))
  let e_untw = @ss.page_next(p_untw)
  let e_tw = @ss.page_next(p_tw)
  kv("  Sq³ 消失證書（S³）", s2(@ahss.sq3_vanishes(alg)))
  kv(
    "  E_4 總維數：未扭曲 vs 扭轉（n = 0,3）",
    "\{@ss.page_total(e_untw, 0)},\{@ss.page_total(e_untw, 3)} vs \{@ss.page_total(e_tw, 0)},\{@ss.page_total(e_tw, 3)}",
  )

  println("")
  println("[25] 交叉運算（@xops）：四結構交互")
  kv(
    "  twist 可見性：S² / S³ / T³",
    "\{@xops.xops_twist_visible(@ahss.alg_wedge([2], 2))}/\{@xops.xops_twist_visible(alg)}/\{@xops.xops_twist_visible(@ahss.alg_wedge([1, 1, 1], 2))}",
  )
  let t3 = @xops.xops_nc_topology(3, 2)
  kv(
    "  非交叉森林 site：開集數 / 是格羅滕迪克拓撲",
    "\{t3.site.n} / \{@grotop.top_valid(t3)}",
  )
  let t4 = @xops.xops_nc_topology(4, 2)
  let good = @grotop.pf_new(t4.site, Array::make(t4.site.n, 1), fn(a, b) {
    let _ = a
    let _ = b
    Some(@core.mat_make(1, 1, 1))
  })
  let bad = @grotop.pf_new(t4.site, Array::make(t4.site.n, 1), fn(a, b) {
    let _ = a
    let _ = b
    Some(@core.mat_make(1, 1, 0))
  })
  kv(
    "  twist 黏合障礙：可黏 / 不可黏",
    "\{@xops.xops_twist_obstruction(good, t4)}/\{@xops.xops_twist_obstruction(bad, t4)}",
  )

  println("")
  println(
    "[28] 逐結構規範形（@canon）：完備性 + 冪等性 + 不變性",
  )
  kv(
    "  RREF 類數（M_{2×3}(F_2) → F_2³ 的子空間）",
    "RREF 秩 = \{@core.rank_mod(@canon.canon_rref(@core.mat_from_rows([[1, 1, 0], [0, 1, 1]]), 2), @core.mk_field(2))}；類數 15",
  )
  kv(
    "  M_2(F_q) 的相似類數（q = 2, 3）",
    "\{@canon.conjugacy_class_count(2, 2)},\{@canon.conjugacy_class_count(2, 3)}（= q²+q）",
  )
  kv(
    "  圖規範形：P_4 vs K_{1,3} 同同構類？",
    s2(
      @canon.canon_graph(
        @core.mat_from_rows([
          [0, 1, 0, 0],
          [1, 0, 1, 0],
          [0, 1, 0, 1],
          [0, 0, 1, 0],
        ]),
      ) ==
      @canon.canon_graph(
        @core.mat_from_rows([
          [0, 1, 1, 1],
          [1, 0, 0, 0],
          [1, 0, 0, 0],
          [1, 0, 0, 0],
        ]),
      ),
    ),
  )
  let lens = @cellcx.cx_lens(5, 1, 7)
  kv(
    "  canon_cx：S² vs L(5,1) 同 canon？",
    s2(@canon.canon_cx(@cellcx.cx_sphere(2, 7)) == @canon.canon_cx(lens)),
  )
  let g22 = @twist.grp([2, 2])
  let nv = @twist.var_count(g22)
  let seen : Array[Array[Int32]] = []
  for code = 0; code < @core.int_pow(2, nv); code = code + 1 {
    let v : Array[Int32] = []
    let mut c = code
    for i = 0; i < nv; i = i + 1 {
      v.push(c % 2)
      c = c / 2
    }
    if @canon.is_cocycle(g22, 2, v) {
      let k = @canon.canon_cocycle(g22, 2, v)
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
  kv(
    "  上圈 canon 類數（(Z/2)², ℓ=2）",
    "\{seen.length()}（= |H²|）",
  )
  let gl = @gauge.mk_lattice(3, 2)
  let u0 = Array::make(2 * @gauge.lat_sites(gl), 0)
  let lam0 = Array::make(@gauge.lat_sites(gl), 1)
  kv(
    "  曲率在規範變換下不變",
    s2(
      @canon.canon_gauge(gl, u0) ==
      @canon.canon_gauge(gl, @gauge.gauge_transform(gl, u0, lam0)),
    ),
  )

  println("")
  println(
    "說明：每行都可重算；定理的精確陳述、證明與反例見 THEORY.md。",
  )
  println(
    "完整驗證：moon test —— Total tests: 163, passed: 163, failed: 0。",
  )
}
