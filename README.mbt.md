# tensorlab

以 MoonBit（穩定版 `moon 0.1.20261023` / `moonc v0.10.17`）實作的數學結構實驗場：
**張量積 · 消元 · 扭曲 K 理論 · 非交叉樹 · 向量叢（格點線叢）· 拉蒙場（Clifford 零模）· Radon 變換 · 有限度量空間**。

理論主檔：[`THEORY.md`](THEORY.md)（定義 `[D-]`／公理 `[Ax-]`／命題 `[P-]`／定理 `[T-]`／推論 `[C-]`／算法 `[E-]`／演變恆定關係 `[Inv-]`，
標籤與各套件的文件註解一一對應）。

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
cmd/main       報告產生器（即時重算 THEORY.md 的數值結論）
```

## 重算

```sh
export PATH="$HOME/.moon/bin:$PATH"
moon check          # 0 errors, 1 warning（nc/moon.pkg 的 core 只被 nc_test 使用）
moon test           # Total tests: 66, passed: 66, failed: 0
moon run cmd/main   # 印出全部數值結論的報告
```

單套件測試請在**根目錄**執行：
`moon test --package username/tensorlab/<core|tensor|nc|twist|gauge|radon|metric|evolve>`
（在套件目錄內跑 `moon test` 會跑整個專案，數字是累計值。）

## 測試分佈（66）

| core | tensor | nc | twist | gauge | radon | metric | evolve |
|---|---|---|---|---|---|---|---|
| 10 | 12 | 10 | 7 | 9 | 5 | 6 | 7 |

## 注意

* 所有算術在 32 位元 `Int` 上進行；乘法先於約化，故一律使用 `p ≤ core.safe_prime_bound() = 46337`。
* 本專案把「哪些猜想被自己的計算否決」也寫成測試與文件（THEORY.md §11）——負面結果同樣可重算。
* 代碼健檢（去重、除錯、死碼清理）的完整紀錄見 [`CODE_HEALTH.md`](CODE_HEALTH.md)，缺陷清單見 THEORY.md §13。
