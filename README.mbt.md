# tensorlab

以 MoonBit（穩定版 `moon 0.1.20261023` / `moonc v0.10.17`）實作的數學結構實驗場：
**張量積 · 消元 · 扭曲 K 理論 · 非交叉樹 · 向量叢（格點線叢）· 拉蒙場（Clifford 零模）· Radon 變換 · 有限度量空間 ·
超化 · 譜化 · 持久賬本 · 五關係 ·
譜序列 · 塞爾 · Adams · 格羅滕迪克拓撲 · 凝聚群 · 扭曲 AHSS · 交叉運算**。

理論主檔：[`THEORY.md`](THEORY.md)（定義 `[D-]`／公理 `[Ax-]`／命題 `[P-]`／定理 `[T-]`／推論 `[C-]`／算法 `[E-]`／演變恆定關係 `[Inv-]`，
標籤與各套件的文件註解一一對應；§14–§18 是本輪新增的超化／譜化／正則表示／賬本／五關係）。

## 套件依賴（單向，避免循環自證）

```
core（F_p 消元、Smith 標準形、整數關係、Rng）
  ├── tensor   展平秩下界、完備秩判定、Cayley 超行列式
  ├── nc       非交叉樹／匹配／三角剖分、翻轉圖、區間 DP、[T-NC-Free]
  ├── twist    H²(G,ℤ/ℓ)、twisted group algebra、扭曲 K₀、規範流
  │     └── gauge   Clifford＝扭曲群代數（拉蒙零模）、ℤ/ℓ 格點線叢與模空間
  ├── radon    有限 Radon 變換、Gram 恆等式、顯式反演、切片定理
  └── metric   度量公理、Gromov–Hausdorff、Vietoris–Rips 同調
evolve         把上述結構放在「演變」下，用消元**導出**恆定關係並轉移到獨立資料族
hyper          超化：每個結構換成「乘積的可能結果集」，並判定六條超群公理
spectral       譜化：特徵多項式、譜、手徵算子、扭曲正則表示的跡
ledger         超級持久賬本：FNV-1a 雜湊鏈（O(1) append、fork、篡改偵測、稽核、重放）
relations      五關係：相對／對偶／對比／蘊含／比率 → 導出擴展定理，並可灌入賬本
cellcx         CW 複形（球面／透鏡／環面／乘積）＋ 持續同調條碼（birth/death 配對）
ss             譜序列引擎（雙次、ker/im、下一頁、張量、q 方向旗標）
serre          塞爾譜序列（Hopf 纖維化、球叢、退化兩列）＋ 與胞腔同調交叉驗證
adams          Adem 關係、最小自由分解 → Ext_A(F₂,F₂)、Adams 頁與莖維數
grotop         有限 site／sieve／覆蓋公理 (T1)(T2)(T3)／層條件／加號構造
condensed      profinite 層級鏈、Z[S]^■、Ext 消失證書、固態性缺口、張量同構
ahss           分次代數上的扭曲 Atiyah–Hirzebruch 譜序列（d₃ = Sq³ + H∪）
dtensor        導出張量積：Koszul 自由分解、Tor = Λ 在 2g 生成元上、Künneth
xops           交叉運算：H³ 可見性、並的可加性、非交叉森林 site、twist 黏合障礙
cmd/main       報告產生器（即時重算 THEORY.md 的數值結論）
```

## 重算

```sh
export PATH="$HOME/.moon/bin:$PATH"
moon check          # 0 errors, 0 warnings
moon test           # Total tests: 144, passed: 144, failed: 0
moon run cmd/main   # 163 行即時重算報告
```

單套件測試請在**根目錄**執行：
`moon test --package username/tensorlab/<pkg>`，`<pkg>` ∈
`core | tensor | nc | twist | gauge | radon | metric | evolve | hyper | spectral | ledger | relations | cellcx | ss | serre | adams | grotop | condensed | ahss | dtensor | xops`
（在套件目錄內跑 `moon test` 會跑整個專案，數字是累計值。）

## 測試分佈（144）

| core | tensor | nc | twist | gauge | radon | metric | evolve | hyper | spectral | ledger | relations |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 10 | 12 | 10 | 8 | 9 | 5 | 6 | 7 | 7 | 12 | 7 | 8 |

| cellcx | ss | serre | adams | grotop | condensed | ahss | dtensor | xops |
|---|---|---|---|---|---|---|---|---|
| 3 | 5 | 4 | 5 | 6 | 5 | 6 | 4 | 5 |

## 注意

* 所有算術在 32 位元 `Int` 上進行；乘法先於約化，故一律使用 `p ≤ core.safe_prime_bound() = 46337`。
* 本專案把「哪些猜想被自己的計算否決」也寫成測試與文件（THEORY.md §11、§18.4）——負面結果同樣可重算。
* 代碼健檢（去重、除錯、死碼清理）的完整紀錄見 [`CODE_HEALTH.md`](CODE_HEALTH.md)，缺陷清單見 THEORY.md §13。
