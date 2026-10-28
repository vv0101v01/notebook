///| stensor —— 張量結構的超化：分次 Kronecker 積、Koszul 號展平、
///| 以及「超 Cayley 不變量不存在」的計算否決。
///|
///|  * `[S-D-grKron]` 分次（Koszul 扭曲）Kronecker 積：齊次 B 作用在
///|    分次張量積上時，矩陣 = (A⊗B)·D，D 為 ±1 對角矩陣
///|    ⟹ `[S-C-KronRank]` rank(A⊗̂B) = rank A · rank B（[P-KronRank] 的超化）；
///|  * `[S-C-KoszulFlat]` 帶 Koszul 號的展平不改變秩（扭曲 = 可逆對角矩陣）；
///|  * `[S-D-InvSearch]` 8 個座標 T_{ijk}（奇偶 = i+j+k mod 2）上的
///|    6 個奇導子 D_E、D_F（OSL(1|1)³ 的無窮小作用）；
///|    `[S-T-OddAlg]` 算子代數 {D_E,D_F} = Euler、D² = 0 由計算釘死；
///|    `[S-NEG-SDet]` 四次不變量 = 常數（純量中心方向的阻礙）。

///| [S-D-grKron] 分次 Kronecker：K = (A⊗B)·D，其中 D 對列 (j,l) 扭曲
///| (−1)^{pb·odd(l)}（pb = B 的齊次奇偶；odd(l) = l 是否落在 B 的奇指標）。
///| odd_cols：B 的欄位奇偶判定（0/1）。
pub fn kron_twisted(
  a : @core.Mat,
  b : @core.Mat,
  p : Int,
  pb : Int,
  odd_cols : Array[Int],
) -> @core.Mat {
  @core.mat_build(a.rows * b.rows, a.cols * b.cols, (i, j) => {
    let ai = i / b.rows
    let bi = i % b.rows
    let aj = j / b.cols
    let bj = j % b.cols
    let av = a.data[ai * a.cols + aj]
    let bv = b.data[bi * b.cols + bj]
    let twist = if pb * odd_cols[bj] % 2 == 1 { p - 1 } else { 1 }
    av * bv % p * twist % p
  })
}

///| 扭曲的顯式對角矩陣 D（驗證 K = (A⊗B)·D 用）。
pub fn kron_twist_diag(
  a : @core.Mat,
  b : @core.Mat,
  p : Int,
  pb : Int,
  odd_cols : Array[Int],
) -> @core.Mat {
  let n = a.cols * b.cols
  let d = @core.mat_make(n, n, 0)
  for j = 0; j < a.cols; j = j + 1 {
    for l = 0; l < b.cols; l = l + 1 {
      let col = j * b.cols + l
      d.data[col * n + col] = if pb * odd_cols[l] % 2 == 1 { p - 1 } else { 1 }
    }
  }
  d
}

///| [S-C-KoszulFlat] 帶號展平：mode-1 展平但欄 (j,k) 乘 (−1)^{[j][k]}
///| （奇偶標記 odd2、odd3 給定）。回傳 (無號展平, 帶號展平, 扭曲對角矩陣)。
pub fn flatten_signed(
  data : Array[Int], // d0×d1×d2 的行主序張量
  d0 : Int,
  d1 : Int,
  d2 : Int,
  odd2 : Array[Int],
  odd3 : Array[Int],
  p : Int,
) -> (@core.Mat, @core.Mat, @core.Mat) {
  let plain = @core.mat_build(d0, d1 * d2, (i, col) => {
    let j = col / d2
    let k = col % d2
    data[(i * d1 + j) * d2 + k] % p
  })
  let signed = @core.mat_build(d0, d1 * d2, (i, col) => {
    let j = col / d2
    let k = col % d2
    let twist = if odd2[j] * odd3[k] % 2 == 1 { p - 1 } else { 1 }
    data[(i * d1 + j) * d2 + k] % p * twist % p
  })
  let n = d1 * d2
  let diag = @core.mat_make(n, n, 0)
  for j = 0; j < d1; j = j + 1 {
    for k = 0; k < d2; k = k + 1 {
      let col = j * d2 + k
      diag.data[col * n + col] = if odd2[j] * odd3[k] % 2 == 1 { p - 1 } else { 1 }
    }
  }
  (plain, signed, diag)
}

pub fn coord_parity(c : Int) -> Int {
  ((c / 4) + ((c / 2) % 2) + (c % 2)) % 2
}

///| 稀疏多項式：monomial 鍵（升冪 4 元組的 9 進位編碼）→ 係數。
pub struct SPoly {
  p : Int
  terms : Map[Int, Int]
}

pub fn spoly_zero(p : Int) -> SPoly {
  SPoly::{ p, terms: Map([]) }
}

pub fn spoly_add_term(f : SPoly, key : Int, coeff : Int) -> SPoly {
  let c = ((coeff % f.p) + f.p) % f.p
  if c == 0 {
    return f
  }
  let out = SPoly::{ p: f.p, terms: copy_map(f.terms) }
  let old = out_terms(out, key)
  let nv = (old + c) % f.p
  if nv == 0 {
    let _ = out.terms.remove(key)
  } else {
    out.terms[key] = nv
  }
  out
}

fn out_terms(f : SPoly, key : Int) -> Int {
  match f.terms.get(key) {
    Some(v) => v
    None => 0
  }
}

fn copy_map(m : Map[Int, Int]) -> Map[Int, Int] {
  let out : Map[Int, Int] = Map([])
  for k, v in m {
    out[k] = v
  }
  out
}

///| 單項鍵：4 個座標（允許重複；奇座標重複 ⇒ 項為 0，由呼叫端避免）。
pub fn monomial_key(cs : Array[Int]) -> Int {
  // 假定 cs 已升冪排序
  cs[0] + 9 * cs[1] + 81 * cs[2] + 729 * cs[3]
}

fn key_decode(key : Int) -> Array[Int] {
  [key % 9, (key / 9) % 9, (key / 81) % 9, (key / 729) % 9]
}

///| 單項乘積的規範化：把有序座標列表排序（記錄反演奇偶號），
///| 奇座標重複 ⇒ 項為零。
fn canon(cs : Array[Int], p : Int) -> (Int, Int)? {
  // 檢查奇座標重複
  let seen_odd : Array[Int] = []
  for c in cs {
    if coord_parity(c) == 1 {
      for s in seen_odd {
        if s == c {
          return None
        }
      }
      let _ = seen_odd.push(c)
    }
  }
  // 反演號：插入排序（僅相鄰交換；相鄰兩奇因子交換時翻號）
  let arr : Array[Int] = []
  for c in cs {
    let _ = arr.push(c)
  }
  let mut sign = 1
  for i = 1; i < arr.length(); i = i + 1 {
    let mut j = i
    while j > 0 && arr[j] < arr[j - 1] {
      if coord_parity(arr[j]) * coord_parity(arr[j - 1]) % 2 == 1 {
        sign = -sign
      }
      let t = arr[j]
      arr[j] = arr[j - 1]
      arr[j - 1] = t
      j = j - 1
    }
  }
  Some((monomial_key(arr), sign % p))
}

///| [S-D-InvSearch] 奇導子：derivation 由 (源座標 → 目標座標 × 係數) 對給定。
///| 對升冪單項以遞迴規則 D(m₁m₂…) = Σ D(m₁)·(其餘) + (−1)^{|m₁|}m₁·D(其餘)。
pub struct OddDer {
  // pairs[s] = (target, coeff)：D(T_s) = coeff·T_target；無條目 ⇒ 0
  pairs : Map[Int, (Int, Int)]
  p : Int
}

pub fn oddder_of(p : Int, pairs : Array[(Int, Int, Int)]) -> OddDer {
  let m : Map[Int, (Int, Int)] = Map([])
  for pair in pairs {
    let (s, t, c) = pair
    m[s] = (t, (((c % p) + p) % p))
  }
  OddDer::{ pairs: m, p }
}

///| 導子對單項（有序座標列表）的作用：回傳 (鍵, 係數) 項列表。
fn der_on_list(d : OddDer, cs : Array[Int]) -> Array[(Int, Int)] {
  let out : Array[(Int, Int)] = []
  let n = cs.length()
  // 遞迴展開：對每個位置 r，D 作用在 cs[r]，前面因子收集奇偶號
  let mut prefix_par = 0
  for r = 0; r < n; r = r + 1 {
    let pair = d.pairs.get(cs[r])
    if pair is Some((target, coeff)) {
      // 項 = (−1)^{prefix_par} · coeff · cs[0..r) · T_target · cs(r..n)\{r}
      let all : Array[Int] = []
      for q = 0; q < n; q = q + 1 {
        if q == r {
          let _ = all.push(target)
        } else {
          let _ = all.push(cs[q])
        }
      }
      // 排序規範化（插入 target 後重排）
      let cn = canon(all, d.p)
      if cn is Some((key, sign)) {
        let total = coeff * sign % d.p
        if prefix_par % 2 == 1 {
          let _ = out.push((key, (d.p - total) % d.p))
        } else {
          let _ = out.push((key, total))
        }
      }
    }
    prefix_par = (prefix_par + coord_parity(cs[r])) % 2
  }
  out
}

///| 導子對多項式的作用。
pub fn spoly_derive(d : OddDer, f : SPoly) -> SPoly {
  let mut out = spoly_zero(d.p)
  for key, coeff in f.terms {
    let cs = key_decode(key)
    let terms = der_on_list(d, cs)
    for pair in terms {
      let (k2, c2) = pair
      out = spoly_add_term(out, k2, coeff * c2)
    }
  }
  out
}

///| 生成全部四次單項（8 座標、4 次；奇座標至多一次）的鍵列表。
pub fn quartic_monomials() -> Array[Int] {
  let keys : Array[Int] = []
  for a = 0; a < 8; a = a + 1 {
    for b = a; b < 8; b = b + 1 {
      for c = b; c < 8; c = c + 1 {
        for e = c; e < 8; e = e + 1 {
          // 奇座標重複檢查
          let arr = [a, b, c, e]
          let mut bad = false
          let seen : Array[Int] = []
          for x in arr {
            if coord_parity(x) == 1 {
              for y in seen {
                if x == y {
                  bad = true
                }
              }
              let _ = seen.push(x)
            }
          }
          if !bad {
            let _ = keys.push(monomial_key(arr))
          }
        }
      }
    }
  }
  keys
}

///| 以鍵構造單項式多項式。
pub fn spoly_of_key(key : Int, p : Int) -> SPoly {
  let f = spoly_zero(p)
  spoly_add_term(f, key, 1)
}

///| 6 個奇導子（OSL(1|1)³ 的作用；leg = 0,1,2；is_up = true 表 E、false 表 F）。
///| 座標約定：leg ℓ 的索引佔 c 的位元（leg0: bit2、leg1: bit1、leg2: bit0）。
///| D_E（leg ℓ）：T_{i=1} ↦ −T_{i=0}（該 leg）；D_F：T_{i=0} ↦ −T_{i=1}。
pub fn odd_derivation(leg : Int, is_up : Bool, p : Int) -> OddDer {
  let bit = if leg == 0 { 4 } else { if leg == 1 { 2 } else { 1 } }
  let pairs : Array[(Int, Int, Int)] = []
  for c = 0; c < 8; c = c + 1 {
    let i = (c / bit) % 2
    if is_up && i == 1 {
      let _ = pairs.push((c, c - bit, p - 1)) // T_{i=1} ↦ −T_{i=0}
    }
    if !is_up && i == 0 {
      let _ = pairs.push((c, c + bit, p - 1)) // T_{i=0} ↦ −T_{i=1}
    }
  }
  oddder_of(p, pairs)
}
