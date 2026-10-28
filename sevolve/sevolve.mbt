///| sevolve —— 演化結構的超化：超對稱演化下的不變量與譜穩定性，
/// 以及把演化過程寫入「持久超帳本」（sledger 雜湊鏈）。
///|
///|  * `[S-D-SusyEvo]` SUSY 演化：D ↦ U·D·V（U、V 可逆）：
///    rank 不變、核維數不變、Witten 指標 = m−n 不變；
///    奇擾動只在掉 rank 的時刻改變核維數（指標仍然不變——跳變相消）；
///|  * `[S-T-EvoStr]` 分次共軛演化 H ↦ G H G⁻¹（G 偶）：
///    charpoly 不變（譜守恆）且 str(H^k) = 0 在每一step成立；
///|  * `[S-C-EvoLedger]` 演化記錄入鏈：每步把 (rank, index, str) 寫入
///    sledger 雜湊鏈；sled_verify 全鏈通過；篡改任一 payload ⟹ 驗證失敗。

///| 隨機可逆矩陣（mod p；重抽直到滿秩）。
pub fn random_invertible(
  n : Int,
  p : Int,
  r : @core.Rng,
) -> @core.Mat {
  let f = @core.mk_field(p)
  let mut m = @core.mat_build(n, n, (_i, _j) => @core.rng_below(r, p))
  let mut tries = 0
  while @core.rank_mod(m, f) != n && tries < 200 {
    m = @core.mat_build(n, n, (_i, _j) => @core.rng_below(r, p))
    tries = tries + 1
  }
  m
}

///| SUSY 演化一步：D ↦ U·D·V（不改變 rank）。
pub fn susy_evolve(
  d : @core.Mat,
  u : @core.Mat,
  v : @core.Mat,
  p : Int,
) -> @core.Mat {
  @core.mat_mul(@core.mat_mul(u, d, p), v, p)
}

///| H = Q² 的偶塊（DᵀD 與 DDᵀ）之分次跡 str(H^k)（mod p；m、n 為 D 的維度）。
pub fn susy_str_pow(
  d : @core.Mat,
  k : Int,
  p : Int,
) -> Int {
  // str(H^k) = tr((DᵀD)^k) − tr((DDᵀ)^k)（Q² 的偶/奇塊）
  let dt = @core.mat_transpose(d)
  let ho = @core.mat_mul(dt, d, p) // m×m
  let he = @core.mat_mul(d, dt, p) // n×n
  let p2 = mat_pow_trace(ho, k, p)
  let p1 = mat_pow_trace(he, k, p)
  ((p2 - p1) % p + p) % p
}

fn mat_pow_trace(a : @core.Mat, k : Int, p : Int) -> Int {
  let n = a.rows
  let mut acc = @core.mat_identity(n)
  for i = 0; i < k; i = i + 1 {
    acc = @core.mat_mul(acc, a, p)
  }
  let mut t = 0
  for i = 0; i < n; i = i + 1 {
    t = (t + acc.data[i * n + i]) % p
  }
  t
}

///| 演化軌跡的帳本化：把每步的不變量寫成 payload 字串。
pub fn evo_payload(
  step : Int,
  rank : Int,
  kernel_sum : Int,
  index : Int,
) -> String {
  "step=\{step};rank=\{rank};ksum=\{kernel_sum};idx=\{index}"
}

///| 隨機么上三角矩陣 A = I + N（N 嚴格上三角）與其逆（有限和）。
pub fn random_unipotent(n : Int, p : Int, r : @core.Rng) -> (@core.Mat, @core.Mat) {
  let nn = @core.mat_build(n, n, (i, j) => {
    if i < j {
      @core.rng_below(r, p)
    } else {
      0
    }
  })
  let eye = @core.mat_identity(n)
  let a = @core.mat_add(eye, nn, p)
  // A⁻¹ = Σ_{k=0}^{n−1} (−N)^k
  let mut term = eye
  let mut acc = eye
  let negn = @core.mat_scale(nn, p - 1, p)
  for k = 1; k < n; k = k + 1 {
    term = @core.mat_mul(term, negn, p)
    acc = @core.mat_add(acc, term, p)
  }
  (a, acc)
}

///| 完整超對稱 Q = [[0, Dᵀ],[D, 0]]（(n+m)×(n+m)，mod p）。
pub fn susy_q(d : @core.Mat) -> @core.Mat {
  let n = d.rows
  let m = d.cols
  let dt = @core.mat_transpose(d)
  @core.mat_build(n + m, n + m, (i, j) => {
    if i < m && j >= m {
      dt.data[i * n + (j - m)]
    } else if i >= m && j < m {
      d.data[(i - m) * m + j]
    } else {
      0
    }
  })
}

///| 分次共軛：G = diag(A, B)（A：m×m、B：n×n）作用 Q ↦ G Q G⁻¹。
pub fn graded_conjugate(
  q : @core.Mat,
  a : @core.Mat,
  ainv : @core.Mat,
  b : @core.Mat,
  binv : @core.Mat,
  p : Int,
) -> @core.Mat {
  let m = a.rows
  let n = b.rows
  let sz = m + n
  // g = diag(A, B)；ginv = diag(A⁻¹, B⁻¹)
  let g = @core.mat_build(sz, sz, (i, j) => {
    if i < m && j < m {
      a.data[i * m + j]
    } else if i >= m && j >= m {
      b.data[(i - m) * n + (j - m)]
    } else {
      0
    }
  })
  let ginv = @core.mat_build(sz, sz, (i, j) => {
    if i < m && j < m {
      ainv.data[i * m + j]
    } else if i >= m && j >= m {
      binv.data[(i - m) * n + (j - m)]
    } else {
      0
    }
  })
  @core.mat_mul(@core.mat_mul(g, q, p), ginv, p)
}
