// ===========================================================================
// catify —— 逐結構範疇化
//
// 一個「範疇」在本檔是**顯式有限線性範疇**：
//   物件 0..n−1；Hom(i,j) 是 F_p 上帶基的向量空間（`hom[i][j]` = 維數）；
//   合成是雙線性映射 mu[i][j][k] : Hom(i,j) ⊗ Hom(j,k) → Hom(i,k)（矩陣，列 = 目標基、
//   欄 = a*dim(j,k)+b）；單位態射 id_i 記為 Hom(i,i) 的基向量 `ids[i]`。
//
// 範疇公理（全部用矩陣恆等式驗，不是口頭聲明）：
//   [Ax-Cat-Assoc]  mu[i][k][l]·(mu[i][j][k] ⊗ I) = mu[i][j][l]·(I ⊗ mu[j][k][l])
//   [Ax-Cat-UnitL]  mu[i][i][j] 在 id_i 那一欄 = 單位
//   [Ax-Cat-UnitR]  mu[i][j][j] 在 id_j 那一欄 = 單位
//
// 去範疇化（decat）= 取同構類的個數；對群胚另給「群胚基數」Σ 1/|Aut|。
// ===========================================================================

///|
/// [D-Cat] 有限線性範疇。
pub struct Cat {
  n : Int32
  hom : Array[Array[Int32]]
  mu : Array[Array[Array[@core.Mat]]]
  ids : Array[Int32]
  p : Int32
}

///|
/// 以「Hom 維數表」建骨架（合成暫設為零矩陣）。
pub fn cat_new(hom : Array[Array[Int32]], p : Int32) -> Cat {
  let n = hom.length()
  let empty = @core.mat_make(0, 0, 0)
  let mu : Array[Array[Array[@core.Mat]]] = Array::makei(n, _ => {
    Array::makei(n, _ => Array::makei(n, _ => empty))
  })
  Cat::{ n, hom, mu, ids: Array::make(n, 0), p, }
}

///|
/// 設定 Hom(i,j)⊗Hom(j,k) → Hom(i,k) 的合成矩陣。
pub fn cat_set_mu(
  c : Cat,
  i : Int32,
  j : Int32,
  k : Int32,
  m : @core.Mat,
) -> Unit {
  c.mu[i][j][k] = m
}

///|
/// 讀取合成矩陣（缺省為零矩陣）。
pub fn cat_mu(c : Cat, i : Int32, j : Int32, k : Int32) -> @core.Mat {
  c.mu[i][j][k]
}

///|
/// Hom 維數。
pub fn cat_dim(c : Cat, i : Int32, j : Int32) -> Int32 {
  if i < 0 || j < 0 || i >= c.n || j >= c.n {
    0
  } else {
    c.hom[i][j]
  }
}

///|
/// 由「合成規則」建範疇：對每個（來源基 a、中間基 b）給出目標基索引（−1 表示零）。
pub fn cat_build(
  hom : Array[Array[Int32]],
  rule : (Int32, Int32, Int32, Int32, Int32) -> Int32,
  p : Int32,
) -> Cat {
  let c = cat_new(hom, p)
  for i = 0; i < c.n; i = i + 1 {
    for j = 0; j < c.n; j = j + 1 {
      for k = 0; k < c.n; k = k + 1 {
        let rows = cat_dim(c, i, k)
        let cols = cat_dim(c, i, j) * cat_dim(c, j, k)
        let m = @core.mat_make(rows, cols, 0)
        for a = 0; a < cat_dim(c, i, j); a = a + 1 {
          for b = 0; b < cat_dim(c, j, k); b = b + 1 {
            let t = rule(i, j, k, a, b)
            if t >= 0 && t < rows {
              m.data[t * cols + a * cat_dim(c, j, k) + b] = (
                  m.data[t * cols + a * cat_dim(c, j, k) + b] + 1
                ) %
                p
            }
          }
        }
        cat_set_mu(c, i, j, k, m)
      }
    }
  }
  c
}

///|
/// 設定第 i 個物件的單位態射在 Hom(i,i) 中的基索引。
pub fn cat_set_id(c : Cat, i : Int32, idx : Int32) -> Unit {
  c.ids[i] = idx
}

///|
/// [T-Cat-Assoc] 結合律（四元組逐格用矩陣乘法比對）。
pub fn cat_assoc(c : Cat) -> Bool {
  let n = c.n
  let mut ok = true
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      for k = 0; k < n; k = k + 1 {
        for l = 0; l < n; l = l + 1 {
          let dij = cat_dim(c, i, j)
          let djk = cat_dim(c, j, k)
          let dkl = cat_dim(c, k, l)
          if dij > 0 && djk > 0 && dkl > 0 {
            // 左：h∘(g∘f)
            let left = @core.mat_mul(
              cat_mu(c, i, k, l),
              cat_kron(cat_mu(c, i, j, k), identity_mat(dkl), c.p),
              c.p,
            )
            // 右：(h∘g)∘f
            let right = @core.mat_mul(
              cat_mu(c, i, j, l),
              cat_kron(identity_mat(dij), cat_mu(c, j, k, l), c.p),
              c.p,
            )
            if !@core.mat_eq_mod(left, right, c.p) {
              ok = false
            }
          }
        }
      }
    }
  }
  ok
}

///|
/// 單位矩陣。
pub fn identity_mat(n : Int32) -> @core.Mat {
  let m = @core.mat_make(n, n, 0)
  for i = 0; i < n; i = i + 1 {
    m.data[i * n + i] = 1
  }
  m
}

///|
/// 克羅內積（本檔自用；與 `@ahss.kron` 同構但避免跨包指令碼差異）。
pub fn cat_kron(a : @core.Mat, b : @core.Mat, p : Int32) -> @core.Mat {
  let rows = a.rows * b.rows
  let cols = a.cols * b.cols
  let m = @core.mat_make(rows, cols, 0)
  for i = 0; i < a.rows; i = i + 1 {
    for j = 0; j < a.cols; j = j + 1 {
      let v = a.data[i * a.cols + j]
      if v != 0 {
        for r = 0; r < b.rows; r = r + 1 {
          for cc = 0; cc < b.cols; cc = cc + 1 {
            let w = b.data[r * b.cols + cc]
            if w != 0 {
              m.data[(i * b.rows + r) * cols + (j * b.cols + cc)] = v * w % p
            }
          }
        }
      }
    }
  }
  m
}

///|
/// [T-Cat-Unit] 左右單位律（只檢查單位態射所在的那一欄）。
pub fn cat_units(c : Cat) -> (Bool, Bool) {
  let n = c.n
  let mut okl = true
  let mut okr = true
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      let dij = cat_dim(c, i, j)
      if dij > 0 {
        // 左單位：mu[i][i][j]（列 Hom(i,j)、欄 Hom(i,i)⊗Hom(i,j)）
        let ml = cat_mu(c, i, i, j)
        let idl = c.ids[i]
        if ml.cols == 0 || ml.rows == 0 {
          // 沒有 Hom(i,i) 的態射 ⟹ 不可能有單位律
          okl = false
        }
        for a = 0; a < dij && ml.cols > 0 && ml.rows > 0; a = a + 1 {
          for r = 0; r < dij; r = r + 1 {
            let want = if r == a { 1 } else { 0 }
            if ml.data[r * ml.cols + idl * dij + a] != want {
              okl = false
            }
          }
        }
        // 右單位：mu[i][j][j]（列 Hom(i,j)、欄 Hom(i,j)⊗Hom(j,j)）
        let mr = cat_mu(c, i, j, j)
        let idr = c.ids[j]
        if mr.cols == 0 || mr.rows == 0 {
          okr = false
        }
        for a = 0; a < dij && mr.cols > 0 && mr.rows > 0; a = a + 1 {
          for r = 0; r < dij; r = r + 1 {
            let want = if r == a { 1 } else { 0 }
            if mr.data[r * mr.cols + a * cat_dim(c, j, j) + idr] != want {
              okr = false
            }
          }
        }
      }
    }
  }
  (okl, okr)
}

///|
/// [T-Cat-Total] **合成全定義**：只要 Hom(i,j)、Hom(j,k) 都非零，合成就不得為零。
///   這條比結合律更細 —— 線性範疇允許「零合成」，於是非傳遞的關係在
///   「結合律」上會**假通過**（兩邊都被零遮住），只有這條抓得到。
pub fn cat_composition_total(c : Cat) -> Bool {
  let mut ok = true
  for i = 0; i < c.n; i = i + 1 {
    for j = 0; j < c.n; j = j + 1 {
      for k = 0; k < c.n; k = k + 1 {
        if cat_dim(c, i, j) > 0 && cat_dim(c, j, k) > 0 {
          let m = cat_mu(c, i, j, k)
          let mut any = false
          for v in m.data {
            if v != 0 {
              any = true
            }
          }
          if !any {
            ok = false
          }
        }
      }
    }
  }
  ok
}

///|
/// [T-Cat-Axioms] 三條公理全過 ⟹ 是一個範疇。
pub fn cat_is_category(c : Cat) -> Bool {
  let (l, r) = cat_units(c)
  cat_assoc(c) && l && r
}

// ---------------------------------------------------------------------------
// 去範疇化
// ---------------------------------------------------------------------------

///|
/// 並查集找根。
fn find_root(p : Array[Int32], x : Int32) -> Int32 {
  let mut cur = x
  while p[cur] != cur {
    cur = p[cur]
  }
  cur
}

///|
/// [E-DeCat] 去範疇化（群胚情形）：連通分量 = 同構類，回傳標籤向量。
pub fn cat_components(c : Cat) -> Array[Int32] {
  let n = c.n
  let par : Array[Int32] = Array::makei(n, i => i)
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      if cat_dim(c, i, j) > 0 {
        let a = find_root(par, i)
        let b = find_root(par, j)
        if a != b {
          par[a] = b
        }
      }
    }
  }
  Array::makei(n, i => find_root(par, i))
}

///|
/// [E-DeCat] 同構類的個數 —— 這就是「去範疇化」得到的**數**。
pub fn decat(c : Cat) -> Int32 {
  let comp = cat_components(c)
  let seen : Array[Int32] = []
  for x in comp {
    let mut has = false
    for y in seen {
      if y == x {
        has = true
      }
    }
    if !has {
      seen.push(x)
    }
  }
  seen.length()
}

// ---------------------------------------------------------------------------
// 有理數（群胚基數用）
// ---------------------------------------------------------------------------

///|
/// [D-Frac] 分子分母皆 Int64 的有理數（已約分、分母為正）。
pub struct Frac {
  num : Int64
  den : Int64
}

///|
/// 最大公因數。
pub fn gcd64(a : Int64, b : Int64) -> Int64 {
  let mut x = if a < 0 { -a } else { a }
  let mut y = if b < 0 { -b } else { b }
  while y != 0 {
    let t = x % y
    x = y
    y = t
  }
  if x == 0 {
    1
  } else {
    x
  }
}

///|
/// 約分。
pub fn frac(num : Int64, den : Int64) -> Frac {
  let g = gcd64(num, den)
  let n0 = num / g
  let d0 = den / g
  if d0 < 0 {
    Frac::{ num: -n0, den: -d0, }
  } else {
    Frac::{ num: n0, den: d0, }
  }
}

///|
/// 加法。
pub fn frac_add(a : Frac, b : Frac) -> Frac {
  frac(a.num * b.den + b.num * a.den, a.den * b.den)
}

///|
/// 是否為整數。
pub fn frac_is_int(a : Frac) -> Bool {
  a.den == 1
}

///|
/// [E-Cardinality] 群胚基數 Σ_{同構類} 1/|Aut(x)|（有限群胚時為有理數）。
pub fn cat_groupoid_cardinality(c : Cat) -> Frac {
  let comp = cat_components(c)
  let seen : Array[Int32] = []
  let mut acc = frac(0, 1)
  for i = 0; i < c.n; i = i + 1 {
    let r = comp[i]
    let mut is_rep = true
    for j = 0; j < i; j = j + 1 {
      if comp[j] == r {
        is_rep = false
      }
    }
    if is_rep {
      let aut = cat_dim(c, i, i)
      acc = frac_add(acc, frac(1, aut.to_int64()))
      seen.push(r)
    }
  }
  let _ = seen
  acc
}

// ---------------------------------------------------------------------------
// 具體範疇：逐結構的範疇化
// ---------------------------------------------------------------------------

///|
/// [E-Cat-Discrete] 集合 ↦ 離散範疇（物件 = 元素，態射 = 恆等）。
///   [T-Cat-Discrete] decat = 元素個數（去範疇化回到原來的數）。
pub fn cat_discrete(n : Int32, p : Int32) -> Cat {
  let hom : Array[Array[Int32]] = Array::makei(n, i => {
    Array::makei(n, j => if i == j { 1 } else { 0 })
  })
  let c = cat_build(
    hom,
    fn(i, j, k, a, b) {
      if i == j && j == k && a == 0 && b == 0 {
        0
      } else {
        -1
      }
    },
    p,
  )
  for i = 0; i < n; i = i + 1 {
    cat_set_id(c, i, 0)
  }
  c
}

///|
/// [E-Cat-Grp] 群 ↦ 單物件範疇 BG（Hom = G，合成 = 群乘法）。
///   [T-Cat-Grp] BG 是範疇 ⟺ G 滿足群公理；decat(BG) = 1；|Aut| = |G|。
pub fn cat_from_group(g : @twist.Grp, p : Int32) -> Cat {
  let n = @twist.grp_order(g)
  let hom : Array[Array[Int32]] = Array::makei(1, _ => [n])
  let code_of = fn(x : Int32) { @twist.grp_of_code(g, x) }
  let c = cat_build(
    hom,
    fn(i, j, k, a, b) {
      let _ = i
      let _ = j
      let _ = k
      @twist.grp_code(g, @twist.grp_add(g, code_of(b), code_of(a)))
    },
    p,
  )
  cat_set_id(c, 0, grp_zero_code(g))
  c
}

///|
/// 群的零元編碼。
fn grp_zero_code(g : @twist.Grp) -> Int32 {
  let n = @twist.grp_order(g)
  let mut z = 0
  for i = 0; i < n; i = i + 1 {
    let v = @twist.grp_of_code(g, i)
    let mut zero = true
    for x in v {
      if x != 0 {
        zero = false
      }
    }
    if zero {
      z = i
    }
  }
  z
}

///|
/// [E-Cat-Thin] 偏序集 ↦ thin 範疇（物件 = 開集，i ≤ j ⟺ 唯一態射）。
///   [T-Cat-Thin] 這是範疇 ⟺ 關係自反且傳遞（非傳遞關係會**破壞結合律**）。
pub fn cat_thin(leq : Array[Array[Bool]], p : Int32) -> Cat {
  let n = leq.length()
  let hom : Array[Array[Int32]] = Array::makei(n, i => {
    Array::makei(n, j => if leq[i][j] { 1 } else { 0 })
  })
  let c = cat_build(
    hom,
    fn(i, j, k, a, b) {
      let _ = a
      let _ = b
      let _ = j
      if leq[i][k] {
        0
      } else {
        -1
      }
    },
    p,
  )
  for i = 0; i < n; i = i + 1 {
    cat_set_id(c, i, 0)
  }
  c
}

///|
/// [E-Cat-Site] site ↦ thin 範疇。
pub fn cat_of_site(s : @grotop.Site) -> Cat {
  cat_thin(s.leq, s.p)
}

///|
/// [E-Cat-Relation] 等價關係 ↦ 群胚（物件 = 資料，i ~ j ⟺ 唯一同構）。
///   [T-Cat-Relation] 這是群胚 ⟺ 關係自反、對稱、傳遞。
pub fn cat_relation_groupoid(rel : Array[Array[Bool]], p : Int32) -> Cat {
  let n = rel.length()
  let hom : Array[Array[Int32]] = Array::makei(n, i => {
    Array::makei(n, j => if rel[i][j] { 1 } else { 0 })
  })
  let c = cat_build(
    hom,
    fn(i, j, k, a, b) {
      let _ = a
      let _ = b
      let _ = j
      if rel[i][k] {
        0
      } else {
        -1
      }
    },
    p,
  )
  for i = 0; i < n; i = i + 1 {
    cat_set_id(c, i, 0)
  }
  c
}

///|
/// [E-Cat-Action] 作用群胚 X//G：物件 = X，Hom(x,y) = {g : g·x = y}。
///   合成 = 群乘法、恆等 = e。decat = 軌道數；群胚基數 = |X|/|G|。
pub fn cat_action_groupoid(
  g : @twist.Grp,
  m : Int32,
  act : (Int32, Int32) -> Int32,
  p : Int32,
) -> Cat {
  let ng = @twist.grp_order(g)
  let hom : Array[Array[Int32]] = Array::makei(m, x => {
    Array::makei(m, y => {
      let mut c = 0
      for k = 0; k < ng; k = k + 1 {
        if act(k, x) == y {
          c = c + 1
        }
      }
      c
    })
  })
  let code_of = fn(x : Int32) { @twist.grp_of_code(g, x) }
  let c = cat_build(
    hom,
    fn(x, y, z, a, b) {
      let _ = x
      let _ = z
      // Hom(x,y) 的第 a 個、Hom(y,z) 的第 b 個：先找出它們的群元素
      let mut ga = -1
      let mut gb = -1
      let mut cnt_a = 0
      let mut cnt_b = 0
      for k = 0; k < ng; k = k + 1 {
        if act(k, x) == y {
          if cnt_a == a {
            ga = k
          }
          cnt_a = cnt_a + 1
        }
        if act(k, y) == z {
          if cnt_b == b {
            gb = k
          }
          cnt_b = cnt_b + 1
        }
      }
      if ga >= 0 && gb >= 0 {
        let prod = @twist.grp_code(
          g,
          @twist.grp_add(g, code_of(gb), code_of(ga)),
        )
        // 找出乘積在 Hom(x,z) 中的序號
        let mut idx = -1
        let mut cnt = 0
        for k = 0; k < ng; k = k + 1 {
          if act(k, x) == z {
            if k == prod {
              idx = cnt
            }
            cnt = cnt + 1
          }
        }
        idx
      } else {
        -1
      }
    },
    p,
  )
  for x = 0; x < m; x = x + 1 {
    // 恆等：e 在 Hom(x,x) 中的序號
    let e = grp_zero_code(g)
    let mut idx = 0
    let mut cnt = 0
    for k = 0; k < ng; k = k + 1 {
      if act(k, x) == x {
        if k == e {
          idx = cnt
        }
        cnt = cnt + 1
      }
    }
    cat_set_id(c, x, idx)
  }
  c
}

///|
/// [E-Cat-Product] 範疇乘積 A × B：物件 = 對、Hom((a,b),(a',b')) = Hom(a,a') ⊗ Hom(b,b')。
///   [T-Cat-Product] 兩範疇的乘積仍是範疇（公理用矩陣驗）。
pub fn cat_product(a : Cat, b : Cat) -> Cat {
  let n = a.n * b.n
  let idx = fn(x : Int32, y : Int32) { x * b.n + y }
  let hom : Array[Array[Int32]] = Array::makei(n, _ => Array::make(n, 0))
  for x = 0; x < a.n; x = x + 1 {
    for y = 0; y < b.n; y = y + 1 {
      for x2 = 0; x2 < a.n; x2 = x2 + 1 {
        for y2 = 0; y2 < b.n; y2 = y2 + 1 {
          hom[idx(x, y)][idx(x2, y2)] = cat_dim(a, x, x2) * cat_dim(b, y, y2)
        }
      }
    }
  }
  let c = cat_build(
    hom,
    fn(p1, q1, r1, s, t) {
      // 解碼三個物件
      let ax = p1 / b.n
      let ay = p1 % b.n
      let qx = q1 / b.n
      let qy = q1 % b.n
      let rx = r1 / b.n
      let ry = r1 % b.n
      let _ = ax
      let _ = ry
      // s = a⊗b 在 Hom(p,q) 的定位；t 在 Hom(q,r)
      let da = cat_dim(a, ax, qx)
      let db = cat_dim(b, ay, qy)
      let sa = s / db
      let sb = s % db
      let da2 = cat_dim(a, qx, rx)
      let db2 = cat_dim(b, qy, ry)
      let ta = t / db2
      let tb = t % db2
      // 目標 (ra, rb)
      let mut res = -1
      let ma = cat_mu(a, ax, qx, rx)
      let mb = cat_mu(b, ay, qy, ry)
      let mut ca = -1
      for r = 0; r < cat_dim(a, ax, rx); r = r + 1 {
        if ma.data[r * ma.cols + sa * cat_dim(a, qx, rx) + ta] != 0 {
          ca = r
        }
      }
      let mut cb = -1
      for r = 0; r < cat_dim(b, ay, ry); r = r + 1 {
        if mb.data[r * mb.cols + sb * cat_dim(b, qy, ry) + tb] != 0 {
          cb = r
        }
      }
      let _ = da
      let _ = da2
      if ca >= 0 && cb >= 0 {
        res = ca * cat_dim(b, ay, ry) + cb
      }
      res
    },
    a.p,
  )
  for x = 0; x < a.n; x = x + 1 {
    for y = 0; y < b.n; y = y + 1 {
      cat_set_id(c, idx(x, y), a.ids[x] * cat_dim(b, y, y) + b.ids[y])
    }
  }
  c
}

// ---------------------------------------------------------------------------
// 函子與自然變換
// ---------------------------------------------------------------------------

///|
/// [D-Functor] 函子：物件映射 + 每個 Hom 的線性映射。
pub struct Functor {
  src : Cat
  dst : Cat
  on_obj : Array[Int32]
  on_hom : Array[Array[@core.Mat]]
  name : String
}

///|
/// 建函子（`on_hom` 給 dimensions 為 src Hom → dst Hom）。
pub fn functor_new(
  src : Cat,
  dst : Cat,
  on_obj : Array[Int32],
  on_hom : Array[Array[@core.Mat]],
  name : String,
) -> Functor {
  Functor::{ src, dst, on_obj, on_hom, name, }
}

///|
/// [T-Functor] 函子性：F(g∘f) = F(g)∘F(f) 且 F(id) = id（矩陣恆等式）。
pub fn functor_valid(f : Functor) -> Bool {
  let s = f.src
  let d = f.dst
  let mut ok = true
  for i = 0; i < s.n; i = i + 1 {
    for j = 0; j < s.n; j = j + 1 {
      for k = 0; k < s.n; k = k + 1 {
        let dij = cat_dim(s, i, j)
        let djk = cat_dim(s, j, k)
        if dij > 0 && djk > 0 {
          // 左邊：F(mu_s(i,j,k))
          let lhs = @core.mat_mul(f.on_hom[i][k], cat_mu(s, i, j, k), s.p)
          // 右邊：mu_d(F i, F j, F k)·(F ⊗ F)
          let rhs = @core.mat_mul(
            cat_mu(d, f.on_obj[i], f.on_obj[j], f.on_obj[k]),
            cat_kron(f.on_hom[i][j], f.on_hom[j][k], s.p),
            s.p,
          )
          if !@core.mat_eq_mod(lhs, rhs, s.p) {
            ok = false
          }
        }
      }
    }
  }
  // 單位
  for i = 0; i < s.n; i = i + 1 {
    let m = f.on_hom[i][i]
    let id_s = s.ids[i]
    let id_d = d.ids[f.on_obj[i]]
    for r = 0; r < m.rows; r = r + 1 {
      let want = if r == id_d { 1 } else { 0 }
      if m.data[r * m.cols + id_s] != want {
        ok = false
      }
    }
  }
  ok
}

///|
/// [D-NatTrans] 自然變換 α: F ⇒ G，分量 α_i : F(i) → G(i)（矩陣，欄 = F(i) 的基向量）。
pub struct NatTrans {
  f : Functor
  g : Functor
  comp : Array[@core.Mat]
}

///|
/// 建自然變換。
pub fn nat_new(f : Functor, g : Functor, comp : Array[@core.Mat]) -> NatTrans {
  NatTrans::{ f, g, comp, }
}

///|
/// [T-NatTrans] 自然性方塊：G(φ)∘α_i = α_j∘F(φ)，對所有基態射 φ 檢查。
pub fn nat_valid(t : NatTrans) -> Bool {
  let f = t.f
  let g = t.g
  let s = f.src
  let d = f.dst
  let mut ok = true
  for i = 0; i < s.n; i = i + 1 {
    for j = 0; j < s.n; j = j + 1 {
      let dij = cat_dim(s, i, j)
      for a = 0; a < dij; a = a + 1 {
        // φ = Hom_s(i,j) 的第 a 個基態射
        // 左：G(φ) ∘ α_i  （α_i: F i → G i；G(φ): G i → G j）
        let gphi : Array[Int32] = []
        for r = 0; r < cat_dim(d, g.on_obj[i], g.on_obj[j]); r = r + 1 {
          gphi.push(g.on_hom[i][j].data[r * g.on_hom[i][j].cols + a])
        }
        let ai : Array[Int32] = []
        for r = 0; r < cat_dim(d, f.on_obj[i], g.on_obj[i]); r = r + 1 {
          ai.push(t.comp[i].data[r * t.comp[i].cols + 0])
        }
        // 左 = mu(Fi, Gi, Gj)·(α_i ⊗ Gφ)
        let m1 = cat_mu(d, f.on_obj[i], g.on_obj[i], g.on_obj[j])
        let left : Array[Int32] = Array::make(m1.rows, 0)
        for r = 0; r < m1.rows; r = r + 1 {
          for p1 = 0; p1 < ai.length(); p1 = p1 + 1 {
            for p2 = 0; p2 < gphi.length(); p2 = p2 + 1 {
              left[r] = (
                  left[r] +
                  m1.data[r * m1.cols + p1 * gphi.length() + p2] *
                  ai[p1] *
                  gphi[p2]
                ) %
                s.p
            }
          }
        }
        // 右 = α_j ∘ F(φ)：mu(Fi, Fj, Gj)·(Fφ ⊗ α_j)
        let fphi : Array[Int32] = []
        for r = 0; r < cat_dim(d, f.on_obj[i], f.on_obj[j]); r = r + 1 {
          fphi.push(f.on_hom[i][j].data[r * f.on_hom[i][j].cols + a])
        }
        let aj : Array[Int32] = []
        for r = 0; r < cat_dim(d, f.on_obj[j], g.on_obj[j]); r = r + 1 {
          aj.push(t.comp[j].data[r * t.comp[j].cols + 0])
        }
        let m2 = cat_mu(d, f.on_obj[i], f.on_obj[j], g.on_obj[j])
        let right : Array[Int32] = Array::make(m2.rows, 0)
        for r = 0; r < m2.rows; r = r + 1 {
          for p1 = 0; p1 < fphi.length(); p1 = p1 + 1 {
            for p2 = 0; p2 < aj.length(); p2 = p2 + 1 {
              right[r] = (
                  right[r] +
                  m2.data[r * m2.cols + p1 * aj.length() + p2] *
                  fphi[p1] *
                  aj[p2]
                ) %
                s.p
            }
          }
        }
        if left != right {
          ok = false
        }
      }
    }
  }
  ok
}

// ---------------------------------------------------------------------------
// 逐結構的範疇化條目：每個結構一個「categorify → decat」往返
// ---------------------------------------------------------------------------

///|
/// [T-Cat-Roundtrip] 通用的往返定理：`categorify` 造出的範疇必須
///   (a) 滿足三條範疇公理、(b) 去範疇化後回到原來的數。
///   回傳 (是範疇?, decat 值)。
pub fn cat_roundtrip(c : Cat) -> (Bool, Int32) {
  (cat_is_category(c), decat(c))
}

///|
/// [E-Cat-RepRes] 格羅滕迪克拓撲的「sieve = 可表函子的子函子」機器驗證：
///   對 site 的每個開集 U，逐一檢查 `sub` 是否為 `y(U)` 的子函子
///   （包含關係 + 在拉回下封閉），並統計個數。
///   [T-Cat-Sieve] 子函子個數 = sieve 個數 = 向下封閉子集的個數。
pub fn sieve_subfunctor_count(s : @grotop.Site, u : Int32) -> (Int32, Int32) {
  let n = s.n
  // y(U)(V) = 1 ⟺ V ⊆ U
  let total = @core.int_pow(2, n)
  let mut sub_count = 0
  let mut sieve_count = 0
  for mask = 0; mask < total; mask = mask + 1 {
    // 子集
    let in_set = Array::make(n, false)
    for i = 0; i < n; i = i + 1 {
      if (mask >> i) % 2 == 1 {
        in_set[i] = true
      }
    }
    // (1) 子函子：集合 ⊆ {V : V ≤ U} 且向下封閉
    let mut is_sub = true
    for i = 0; i < n; i = i + 1 {
      if in_set[i] && !s.leq[i][u] {
        is_sub = false
      }
      if in_set[i] {
        for j = 0; j < n; j = j + 1 {
          if s.leq[j][i] && !in_set[j] {
            is_sub = false
          }
        }
      }
    }
    if is_sub {
      sub_count = sub_count + 1
    }
    // (2) sieve：同一個定義（交叉檢核用）
    if @grotop.sieve_is_down_closed(s, in_set) && in_set.length() == n {
      let mut ok = true
      for i = 0; i < n; i = i + 1 {
        if in_set[i] && !s.leq[i][u] {
          ok = false
        }
      }
      if ok {
        sieve_count = sieve_count + 1
      }
    }
  }
  (sub_count, sieve_count)
}

///|
/// [T-Cat-Euler] 鏈複形的範疇化：把胞腔複形看成「分次自由模的複形」，
///   其歐拉特徵 = Σ(−1)^k dim C_k = Σ(−1)^k dim H_k（同調是去範疇化）。
///   回傳 (胞腔版, 同調版)。
pub fn cat_euler_pair(cx : @cellcx.CellCx) -> (Int32, Int32) {
  (@cellcx.cx_euler(cx), @cellcx.cx_euler_betti(cx))
}

///|
/// [E-Cat-Monoid] 單物件範疇的「合成表」是否就是原群的乘法表（逐項比對）。
pub fn cat_group_table_matches(c : Cat, g : @twist.Grp) -> Bool {
  if c.n != 1 {
    return false
  }
  let n = @twist.grp_order(g)
  if cat_dim(c, 0, 0) != n {
    return false
  }
  let m = cat_mu(c, 0, 0, 0)
  let mut ok = true
  for a = 0; a < n; a = a + 1 {
    for b = 0; b < n; b = b + 1 {
      let want = @twist.grp_code(
        g,
        @twist.grp_add(g, @twist.grp_of_code(g, b), @twist.grp_of_code(g, a)),
      )
      for r = 0; r < n; r = r + 1 {
        let expect = if r == want { 1 } else { 0 }
        if m.data[r * m.cols + a * n + b] != expect % c.p {
          ok = false
        }
      }
    }
  }
  ok
}

// ---------------------------------------------------------------------------
// 分次對象的範疇化：歐拉特徵是「有號維數和」
// ---------------------------------------------------------------------------

///|
/// [E-Degraded] 分次向量空間的**去範疇化**：歐拉特徵 Σ(−1)^k dim V_k。
///   這是「一個數」的範疇化方向的反面：分次空間 → 數。
pub fn graded_euler(dims : Array[Int32]) -> Int32 {
  let mut s = 0
  for k = 0; k < dims.length(); k = k + 1 {
    let sign = if k % 2 == 0 { 1 } else { -1 }
    s = s + sign * dims[k]
  }
  s
}

///|
/// [T-Cat-FacePoset] 單純複形的**面偏序**（face poset）↦ thin 範疇。
///   物件 = 面、σ ≤ τ ⟺ σ ⊆ τ。decat = 1（有最小元 ⟹ 連通）。
pub fn cat_face_poset(faces : Array[Array[Int32]], p : Int32) -> Cat {
  let n = faces.length()
  let leq : Array[Array[Bool]] = Array::makei(n, i => {
    Array::makei(n, j => {
      let mut sub = true
      for x in faces[i] {
        let mut has = false
        for y in faces[j] {
          if x == y {
            has = true
          }
        }
        if !has {
          sub = false
        }
      }
      sub
    })
  })
  cat_thin(leq, p)
}

///|
/// [E-Cat-Classes] 由「類的鍵」建群胚：物件 = 資料點，i、j 之間恰一個同構 ⟺ 鍵相同。
///   這是「quotient（去範疇化得到的集合）的範疇化」：把等價關係的**見證**變成態射。
///   [T-Cat-Canon] `decat(cat_class_groupoid(keys)) = #{相異鍵}` —— 即 canon 的類數。
///   註：此構造只填 Hom（供 decat 與基數用），不做公理檢查（大型 n 的 n⁴ 檢查不划算）。
pub fn cat_class_groupoid(keys : Array[Array[Int32]]) -> Cat {
  let n = keys.length()
  let hom : Array[Array[Int32]] = Array::makei(n, i => {
    Array::makei(n, j => if keys[i] == keys[j] { 1 } else { 0 })
  })
  let c = cat_new(hom, 2)
  for i = 0; i < n; i = i + 1 {
    cat_set_id(c, i, 0)
  }
  c
}

///|
/// 相異鍵的個數（與 `decat(cat_class_groupoid(keys))` 必須相等）。
pub fn distinct_keys(keys : Array[Array[Int32]]) -> Int32 {
  let seen : Array[Array[Int32]] = []
  for k in keys {
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
  seen.length()
}

///|
/// 把矩陣展平成整數鍵（`@canon` 的鍵也可以用它比較）。
pub fn canon_flatten(m : @core.Mat) -> Array[Int32] {
  m.data.copy()
}

///|
/// [E-Cat-CanonKeys] n 邊形上所有單弦的 canon 鍵（`canon` × `nc` × `catify` 的橋）。
///   5 邊形給出 10 條弦，只有 2 個鍵（邊 vs 對角線）。
pub fn dihedral_class_keys(n : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for a = 0; a < n; a = a + 1 {
    for b = a + 1; b < n; b = b + 1 {
      out.push(@canon.canon_dihedral(n, [@nc.chord(a, b)]))
    }
  }
  out
}
