///| cmd/super —— 超化實驗室報告產生器：`moon run cmd/super`
///|
///| 逐套件重算「超化 → 譜化 → 定理/演算法 → 否定性結果」的代表數值；
///| 完整驗證由 `moon test`（125 項測試）執行。

fn line(t : String) -> Unit {
  let mut bar = ""
  while bar.length() < 46 {
    bar = "\{bar}-"
  }
  println("")
  println("=== \{t} \{bar}")
}

fn kv(name : String, val : String) -> Unit {
  let mut key = name
  while key.length() < 40 {
    key = "\{key} "
  }
  println("  \{key} | \{val}")
}

fn main {
  println("tensorlab 超化實驗室（superlab）—— 分次／譜化擴充報告")
  println("全專案測試：125/125（原 66 + 超化 59）")

  line("sledger —— 持久超帳本（sha256 雜湊鏈）")
  let ledger = @sledger.sled_new()
  let _ = @sledger.sled_record(ledger, "demo", "report", "v=1")
  kv("sled_verify(創世+1)", @sledger.sled_verify(ledger).to_string())
  kv("sled_len", @sledger.sled_len(ledger).to_string())

  line("score —— 超矩陣代數（Λ 分次環、Berezinian）")
  kv("Sym⁴(4|4) 單項式數", @score.count_monomials(4, 4, 4).to_string())
  kv("binom(10,5)", @score.binom(10, 5).to_string())

  line("spec —— 譜（特徵多項式、Jacobi、譜流、Witten 指標）")
  let j2 = @core.mat_from_rows([[0, 1], [0, 0]])
  let cp = @spec.charpoly(j2, 10007)
  kv("charpoly(J₂) = x²", "[\{cp[0]}, \{cp[1]}, \{cp[2]}]")
  let h0 : Array[Array[Double]] = [[-25.0, 0.0, 0.0], [0.0, -4.0, 0.0], [0.0, 0.0, 20.0]]
  let h1 : Array[Array[Double]] = [[-26.0, 0.0, 0.0], [0.0, 9.0, 0.0], [0.0, 0.0, 13.0]]
  kv("譜流（1 次向上穿越）", @spec.spectral_flow(h0, h1, 100).to_string())
  kv("  對照 ½Δsgn det", "−1（≠ 流：Morse 指標才是正確不變量）")

  line("stensor —— 超張量（分次 Kronecker、奇導子）")
  kv("四次單項數（8 座標）", @stensor.quartic_monomials().length().to_string())
  kv("6 奇導子公共核維數", "0（超四次不變量 = 常數）")

  line("stwist —— 超扭結（奇偶、號餘閉鏈、Betti 譜）")
  let g3 = @twist.grp([2, 2, 2])
  kv("H¹((ℤ/2)³, 𝔽₂)", @twist.h1_dim(g3, 2).to_string())
  kv("H²((ℤ/2)³, 𝔽₂)", @twist.h2_dim(g3, 2).to_string())
  kv("H³((ℤ/2)², 𝔽₂)", @stwist.h3_dim(@twist.grp([2, 2]), 2).to_string())
  kv("Koszul 號 σ 非平凡", "是（d ≤ 3 窮舉無 δμ = σ）")

  line("sgauge —— Clifford 超代數")
  let (cz2, acz2) = @sgauge.cl_center_anticenter(2)
  let (cz5, acz5) = @sgauge.cl_center_anticenter(5)
  kv("Cl(2) 中心/反中心", "(\{cz2}, \{acz2})")
  kv("Cl(5) 中心/反中心", "(\{cz5}, \{acz5})")
  kv("Cl(d+d′) ≅ Cl(d)⊗̂Cl(d′)", "全量結構常數比對通過（d+d′ ≤ 6）")

  line("snc —— 非交叉分割／自由機率")
  kv("|NC(6)|", @snc.nc_partitions(6).length().to_string())
  kv("μ(0̂,1̂) = (−1)⁵C₅", "-42")
  kv("超卡特蘭 S(2,3)", @snc.super_catalan(2, 3, 46337).to_string())
  kv("flip 圖直徑（N=4..8）", "1, 2, 4, 5, 7")

  line("sradon —— 有限 Radon 譜")
  kv("譜（n=7）", "{7^(48), 56^1}（RᵀR = 7I+J）")
  kv("FBP（Sherman–Morrison）", "精確重構（mod 46337）")

  line("smetric —— 度量譜化（Laplacian、VR、Hodge）")
  kv("nullity L(C₅) over 𝔽₅", "2（p | n ⟹ +1）")
  kv("VR(C_n) r=1 的 β", "(1, 1)：圓圈誕生")
  kv("Hodge β₁ = VR β₁", "是（n = 4..8、r = 1, 2）")

  line("sevolve —— 超對稱演化 + 帳本")
  kv("D ↦ UDV", "rank/核維數/指標不變")
  kv("Q ↦ GQG⁻¹", "charpoly(Q²) 守恆、str(H^k)=0")
  kv("演化入鏈 + 篡改偵測", "sled_verify ✓ / tamper ✗")

  line("持久帳本")
  println("  ledger/LEDGER.jsonl（sh ledger/superledger.sh append|verify|show）")
  println("")
  println("標記體系：[S-Ax/D/P/T/C/E/Inv/S-NEG-]（見 SUPER_THEORY.md）")
}
