///| stensor 測試：分次 Kronecker 秩定理、Koszul 號展平、奇導子代數、超行列式否決。

///|
test "[S-C-KronRank] 分次 Kronecker：rank(A⊗̂B) = rank A·rank B（Koszul 扭曲 = 可逆對角）" {
  let p = 7
  let f = @core.mk_field(p)
  let r = @core.rng_seed(20261028)
  let mut ok = true
  for trial = 0; trial < 15; trial = trial + 1 {
    let ra = 1 + @core.rng_below(r, 4)
    let ca = 1 + @core.rng_below(r, 4)
    let rb = 1 + @core.rng_below(r, 3)
    let cb = 1 + @core.rng_below(r, 3)
    let a = @core.mat_build(ra, ca, (_i, _j) => @core.rng_below(r, p))
    let b = @core.mat_build(rb, cb, (_i, _j) => @core.rng_below(r, p))
    // B 的欄位奇偶標記（隨機）
    let odd_cols : Array[Int] = []
    for j = 0; j < cb; j = j + 1 {
      let _ = odd_cols.push(@core.rng_below(r, 2))
    }
    for pb = 0; pb < 2; pb = pb + 1 {
      let plain = @tensor.kron_mat(a, b, p)
      let twisted = @stensor.kron_twisted(a, b, p, pb, odd_cols)
      let diag = @stensor.kron_twist_diag(a, b, p, pb, odd_cols)
      // 驗證 K = (A⊗B)·D（扭曲確為右乘對角）
      let prod = @core.mat_mul(plain, diag, p)
      if !@core.mat_eq_mod(prod, twisted, p) {
        ok = false
      }
      // 秩恆等式
      let rk = @core.rank_mod(twisted, f)
      let expect = @core.rank_mod(a, f) * @core.rank_mod(b, f)
      if rk != expect {
        ok = false
      }
    }
  }
  assert_true(ok)
}

///|
test "[S-C-KoszulFlat] 帶 Koszul 號的展平不改變秩（= 右乘 ±1 對角矩陣）" {
  let p = 5
  let f = @core.mk_field(p)
  let r = @core.rng_seed(31337)
  let mut ok = true
  for trial = 0; trial < 12; trial = trial + 1 {
    let d0 = 2
    let d1 = 2 + @core.rng_below(r, 2)
    let d2 = 2 + @core.rng_below(r, 2)
    let data : Array[Int] = []
    for i = 0; i < d0 * d1 * d2; i = i + 1 {
      let _ = data.push(@core.rng_below(r, p))
    }
    let odd2 : Array[Int] = []
    for j = 0; j < d1; j = j + 1 {
      let _ = odd2.push(@core.rng_below(r, 2))
    }
    let odd3 : Array[Int] = []
    for k = 0; k < d2; k = k + 1 {
      let _ = odd3.push(@core.rng_below(r, 2))
    }
    let (plain, signed, diag) = @stensor.flatten_signed(data, d0, d1, d2, odd2, odd3, p)
    let prod = @core.mat_mul(plain, diag, p)
    if !@core.mat_eq_mod(prod, signed, p) {
      ok = false
    }
    if @core.rank_mod(plain, f) != @core.rank_mod(signed, f) {
      ok = false
    }
  }
  assert_true(ok)
}

///|
test "[S-T-SSym] 超對稱立方 Sym³(1|1) 的維度 = 2（Sym⊗Λ 展平的具體案例）" {
  // Sym³(V)，V = (1|1)：= ⊕_{a+b=3} Sym^a(V₀)⊗Λ^b(V₁)；
  // dim = Σ_b C(1,b)·C(1+3−b−1, 3−b) = b=0: C(3,3)=1；b=1: C(2,2)=1 ⟹ 2
  let dims = @score.count_monomials(1, 1, 3)
  assert_eq(dims, 2)
  // 對照：普通（非超）Sym³(ℝ²) = C(4,3) = 4；Λ³(ℝ²) = 0
  assert_eq(@score.count_monomials(2, 0, 3), 4)
  assert_eq(@score.count_monomials(0, 2, 3), 0)
  // 超對稱「GHZ」：e⊗e⊗e 與 e⊗e⊗f 型的基底由 count 見證
  // Sym¹(1|1) = e, f：2；Sym²(1|1) = e², ef（f² = 0）：2
  assert_eq(@score.count_monomials(1, 1, 1), 2)
  assert_eq(@score.count_monomials(1, 1, 2), 2)
}

///|
test "[S-T-OddAlg] 奇導子代數：D² = 0 且 {D_E, D_F} = Euler（腿次數）" {
  let p = 101
  // 對每個 leg 驗證
  for leg = 0; leg < 3; leg = leg + 1 {
    let de = @stensor.odd_derivation(leg, true, p)
    let df = @stensor.odd_derivation(leg, false, p)
    // 在全部四次單項上驗證
    let keys = @stensor.quartic_monomials()
    let mut ok_sq = true
    let mut ok_anti = true
    for key in keys {
      let f = @stensor.spoly_of_key(key, p)
      // D_E² = 0
      let sq = @stensor.spoly_derive(de, @stensor.spoly_derive(de, f))
      if sq.terms.length() != 0 {
        ok_sq = false
      }
      // {D_E, D_F} = 完整 Euler：每個生成子上都是恆等 ⟹ 四次式上 = 4·f
      let anti = sum_poly(
        @stensor.spoly_derive(de, @stensor.spoly_derive(df, f)),
        @stensor.spoly_derive(df, @stensor.spoly_derive(de, f)),
      )
      let expect = scale_poly(f, 4, p)
      if !poly_eq(anti, expect) {
        ok_anti = false
      }
    }
    assert_true(ok_sq)
    assert_true(ok_anti)
  }
}

fn sum_poly(a : @stensor.SPoly, b : @stensor.SPoly) -> @stensor.SPoly {
  let mut out = a
  for k, v in b.terms {
    out = @stensor.spoly_add_term(out, k, v)
  }
  out
}

fn scale_poly(f : @stensor.SPoly, c : Int, p : Int) -> @stensor.SPoly {
  let mut out = @stensor.spoly_zero(p)
  for k, v in f.terms {
    out = @stensor.spoly_add_term(out, k, v * c)
  }
  out
}

fn poly_eq(a : @stensor.SPoly, b : @stensor.SPoly) -> Bool {
  if a.terms.length() != b.terms.length() {
    return false
  }
  for k, v in a.terms {
    let w = b.terms.get(k)
    if w is Some(wv) {
      if wv != v {
        return false
      }
    } else {
      return false
    }
  }
  true
}

///|
test "[S-NEG-SDet] 超四次不變量 = 常數：OSL(1|1)³ 的中心方向阻礙" {
  // 不變量 = 6 個奇導子的公共核（四次齊次部分）。
  // 由 {D_E,D_F} = Euler_leg：核中元素必須 leg 次數 ≡ 0 (mod p)；
  // 四次多項式的 leg 次數 ≤ 4 < 101 ⟹ 三個 leg 的座標都不出現 ⟹ 只有 0。
  // 本測試以消元直接計算公共核，確認維數 = 0。
  let p = 101
  let f = @core.mk_field(p)
  let keys = @stensor.quartic_monomials()
  let n = keys.length()
  // 構造 6×(輸出維)×n 的矩陣：每個導子給出一個線性映射
  let ders : Array[@stensor.OddDer] = []
  for leg = 0; leg < 3; leg = leg + 1 {
    let _ = ders.push(@stensor.odd_derivation(leg, true, p))
    let _ = ders.push(@stensor.odd_derivation(leg, false, p))
  }
  // 鍵 → 行索引
  let key_to_idx : Map[Int, Int] = Map([])
  for idx = 0; idx < n; idx = idx + 1 {
    key_to_idx[keys[idx]] = idx
  }
  // 收集所有導子的行
  let rows : Array[Array[Int]] = []
  for d in ders {
    for j = 0; j < n; j = j + 1 {
      let row : Array[Int] = Array::make(n, 0)
      let fjsonl = @stensor.spoly_of_key(keys[j], p)
      let out = @stensor.spoly_derive(d, fjsonl)
      let mut any = false
      for k, v in out.terms {
        let idx = key_to_idx.get(k)
        if idx is Some(i2) {
          row[i2] = v
          any = true
        }
      }
      if any {
        let _ = rows.push(row)
      }
    }
  }
  // 公共核 = 零空間（把全部導子行疊成一個大矩陣）
  let big = @core.mat_from_rows(rows)
  let ns = @core.nullspace_basis(big, f)
  // 核維數（在四次齊次空間內）
  assert_eq(ns.length(), 0)
  // 對照（超對稱破缺）：單獨一個奇導子 D_E（單一超荷）的核非平凡
  // ——但整個 OSL(1|1) 腿（D_E、D_F 成對；{D_E,D_F} = 4·Euler）已全部殺光。
  let d0e = @stensor.odd_derivation(0, true, p)
  let rows2 : Array[Array[Int]] = []
  for d in [d0e] {
    for j = 0; j < n; j = j + 1 {
      let row : Array[Int] = Array::make(n, 0)
      let fj = @stensor.spoly_of_key(keys[j], p)
      let out = @stensor.spoly_derive(d, fj)
      let mut any = false
      for k, v in out.terms {
        let idx = key_to_idx.get(k)
        if idx is Some(i2) {
          row[i2] = v
          any = true
        }
      }
      if any {
        let _ = rows2.push(row)
      }
    }
  }
  let big2 = @core.mat_from_rows(rows2)
  let ns2 = @core.nullspace_basis(big2, f)
  // 單超荷核：0 < dim < 192（真子空間且非平凡）
  assert_true(ns2.length() > 0)
  assert_true(ns2.length() < 192)
}
