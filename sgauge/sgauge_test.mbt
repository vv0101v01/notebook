///| sgauge 測試：單項 Clifford、中心／反中心、分次張量積、γ 譜、格子 Dirac。

///|
test "[S-D-ClMono] 單項 Clifford：結合律、分次相容、γᵢ² = qᵢ" {
  let p = 7
  let r = @core.rng_seed(555)
  let mut ok = true
  for d = 1; d <= 6; d = d + 1 {
    // 隨機 qᵢ ∈ {1, −1}
    let q : Array[Int] = []
    for i = 0; i < d; i = i + 1 {
      if @core.rng_below(r, 2) == 0 {
        let _ = q.push(1)
      } else {
        let _ = q.push(p - 1)
      }
    }
    if !@sgauge.cl_check_assoc(d, q, p, 200, r) {
      ok = false
    }
    // γᵢ·γᵢ = qᵢ（空交叉補上後 = q_i）
    for i = 0; i < d; i = i + 1 {
      let (c, w) = @sgauge.cl_mul(1 << i, 1 << i, q, p)
      if c != q[i] % p || w != 0 {
        ok = false
      }
    }
    // {γᵢ, γⱼ} = 0（i ≠ j）
    for i = 0; i < d; i = i + 1 {
      for j = 0; j < d; j = j + 1 {
        if i != j {
          let (c1, _) = @sgauge.cl_mul(1 << i, 1 << j, q, p)
          let (c2, _) = @sgauge.cl_mul(1 << j, 1 << i, q, p)
          if (c1 + c2) % p != 0 {
            ok = false
          }
        }
      }
    }
  }
  assert_true(ok)
}

///|
test "[S-T-ClCenter] 中心／反中心表：d 偶 (1,1)、d 奇 (2,0)" {
  for d = 1; d <= 6; d = d + 1 {
    let (cz, acz) = @sgauge.cl_center_anticenter(d)
    if d % 2 == 0 {
      assert_eq(cz, 1)
      assert_eq(acz, 1) // 反中心 = ω·中心
    } else {
      assert_eq(cz, 2) // 中心 = span{1, ω}
      assert_eq(acz, 0)
    }
  }
}

///|
test "[S-T-ClGrTensor] Cl(d+d′) ≅ Cl(d) ⊗̂ Cl(d′)（全量結構常數）" {
  let p = 5
  let r = @core.rng_seed(999)
  for d1 = 0; d1 <= 3; d1 = d1 + 1 {
    for d2 = 0; d2 <= 3; d2 = d2 + 1 {
      if d1 + d2 >= 2 && d1 + d2 <= 6 {
        let d = d1 + d2
        let q : Array[Int] = []
        for i = 0; i < d; i = i + 1 {
          if @core.rng_below(r, 2) == 0 {
            let _ = q.push(1)
          } else {
            let _ = q.push(p - 1)
          }
        }
        assert_true(@sgauge.grtensor_check(d1, d2, q, p))
      }
    }
  }
}

///|
test "[S-D-GammaSpec] γ 矩陣譜恆等式：反交換、無跡單項、體積元平方" {
  let p = 17
  for d = 2; d <= 6; d = d + 1 {
    let g = @gauge.gamma_mats(d, p)
    let n = g[0].rows
    let eye = @core.mat_identity(n)
    // {γᵢ, γⒿ} = 2δᵢⒿ
    for i = 0; i < d; i = i + 1 {
      for j = 0; j < d; j = j + 1 {
        let s = @core.mat_add(
          @core.mat_mul(g[i], g[j], p),
          @core.mat_mul(g[j], g[i], p),
          p,
        )
        // want = 2δᵢⒿ·I（對角 2、非對角 0）
        for k = 0; k < n * n; k = k + 1 {
          let on_diag = k / n == k % n
          let want = if i == j && on_diag { 2 % p } else { 0 }
          if ((s.data[k] - want) % p + p) % p != 0 {
            assert_false(true)
          }
        }
      }
    }
    // 體積元 ω = γ₁⋯γ_d：ω² = (−1)^{d(d−1)/2}（qᵢ = 1）
    let mut w = eye
    for i = 0; i < d; i = i + 1 {
      w = @core.mat_mul(w, g[i], p)
    }
    let w2 = @core.mat_mul(w, w, p)
    let sign = if d * (d - 1) / 2 % 2 == 0 { 1 } else { p - 1 }
    let want = @core.mat_scale(eye, sign, p)
    if !@core.mat_eq_mod(w2, want, p) {
      assert_false(true)
    }
    // tr(ω)：d 偶 ⟹ 0；d 奇 ⟹ ω 中央（純量矩陣），跡 ≠ 0
    if d % 2 == 0 {
      if @sgauge.mat_trace(w, p) != 0 {
        assert_false(true)
      }
    } else {
      let mut scalar = true
      for k = 0; k < n * n; k = k + 1 {
        let on_diag = k / n == k % n
        if !on_diag && w.data[k] != 0 {
          scalar = false
        }
      }
      assert_true(scalar) // ω ∝ I（d 奇：中心由 1 與 ω 撐起）
      if @sgauge.mat_trace(w, p) == 0 {
        assert_false(true)
      }
    }
    // 所有非空單項 γ_S 無跡（d 奇時的唯一例外：滿集 S = ω 中央純量）
    let mut ok_tr = true
    let mut sset = 1
    while sset < (1 << d) {
      let is_vol_full = d % 2 == 1 && sset == (1 << d) - 1
      let mut m = eye
      let mut b = 0
      while b < d {
        if ((sset >> b) & 1) == 1 {
          m = @core.mat_mul(m, g[b], p)
        }
        b = b + 1
      }
      if !is_vol_full && @sgauge.mat_trace(m, p) != 0 {
        ok_tr = false
      }
      if is_vol_full && @sgauge.mat_trace(m, p) == 0 {
        ok_tr = false // d 奇：ω = c·I，c ≠ 0 ⟹ 跡非零（對照組）
      }
      sset = sset + 1
    }
    assert_true(ok_tr)
  }
}

///|
test "[S-D-LatDirac] 格子 Dirac：D² = d(I⊗A²)；分次跡 tr(ΠD^{2k}) = 0" {
  let p = 17
  let i_unit = 4 // 4² = 16 ≡ −1 (mod 17)
  // 手性算子 Π 僅在 d 偶時存在（d 奇：ω 中央，無法翻轉所有 γ 的號）
  for d = 2; d <= 4; d = d + 2 {
    let n_lat = 3
    let g = @gauge.gamma_mats(d, p)
    let sp = g[0].rows
    let a = @sgauge.shift_mat(n_lat, p)
    let eye_sp = @core.mat_identity(sp)
    let eye_lat = @core.mat_identity(n_lat)
    // D = Σᵢ γᵢ ⊗ A
    let mut dmat = @core.mat_make(sp * n_lat, sp * n_lat, 0)
    for i = 0; i < d; i = i + 1 {
      dmat = @core.mat_add(dmat, @tensor.kron_mat(g[i], a, p), p)
    }
    // D² = d·(I⊗A²)
    let d2 = @core.mat_mul(dmat, dmat, p)
    let a2 = @core.mat_mul(a, a, p)
    let want = @core.mat_scale(@tensor.kron_mat(eye_sp, a2, p), d, p)
    if !@core.mat_eq_mod(d2, want, p) {
      assert_false(true)
    }
    // Π = i^{d/2}·ω（d 偶）：Π² = I、ΠγᵢΠ = −γᵢ
    let mut w = eye_sp
    for i = 0; i < d; i = i + 1 {
      w = @core.mat_mul(w, g[i], p)
    }
    let m = d / 2
    let mut ipow = 1
    for k = 0; k < m; k = k + 1 {
      ipow = ipow * i_unit % p
    }
    let par = @core.mat_scale(w, ipow, p) // Π
    let par2 = @core.mat_mul(par, par, p)
    if !@core.mat_eq_mod(par2, eye_sp, p) {
      assert_false(true)
    }
    // ΠγᵢΠ = −γᵢ
    for i = 0; i < d; i = i + 1 {
      let conj = @core.mat_mul(@core.mat_mul(par, g[i], p), par, p)
      let neg = @core.mat_scale(g[i], p - 1, p)
      if !@core.mat_eq_mod(conj, neg, p) {
        assert_false(true)
      }
    }
    // 分次跡消失：tr((Π⊗I)·D^{2k}) = 0，k = 1..3
    let pbig = @tensor.kron_mat(par, eye_lat, p)
    let mut hk = d2
    for k = 1; k <= 3; k = k + 1 {
      let tr = @sgauge.mat_trace(@core.mat_mul(pbig, hk, p), p)
      if tr != 0 {
        assert_false(true)
      }
      hk = @core.mat_mul(hk, d2, p)
    }
    // 對照：普通跡 tr(D^{2}) ≠ 0（D² = d(I⊗A²)，tr = d·2^m·tr(A²)）
    let tr_plain = @sgauge.mat_trace(d2, p)
    let tr_a2 = @sgauge.mat_trace(a2, p)
    if tr_plain != d * sp % p * tr_a2 % p {
      assert_false(true)
    }
  }
}
