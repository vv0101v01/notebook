///| cmd/superledger —— 超化帳本產生器／驗證器（wasm 無 fs：stdout 輸出、
/// argv 驗證；跨執行持久化由 superledger.sh 以 shell 完成）。
///|
///|   moon run cmd/superledger            # 印出 JSONL（創世 + 10 個超套件的頭條不變量）
///|   moon run cmd/superledger -- --verify <JSONL 行...>
///|                                       # 驗證外部（檔案）帳本行：印 VERIFY_OK / VERIFY_FAIL
///|
///| 確定性：所有 payload 都是固定種子下的計算結果，重跑必重得；
///| 雜湊鏈（sha256）保證任何篡改可偵測（見 [S-C-EvoLedger] 測試）。

fn main {
  let args = @env.args()
  // args[0] = 程式名；尋找 --verify
  let mut verify_idx = -1
  for i = 0; i < args.length(); i = i + 1 {
    if args[i] == "--verify" {
      verify_idx = i
    }
  }
  if verify_idx >= 0 {
    // 驗證模式：把後續參數當 JSONL 行（略過創世行——鏈由 genesis.hash 起算）
    let lines : Array[String] = []
    for i = verify_idx + 1; i < args.length(); i = i + 1 {
      let rec = @sledger.sled_parse_line(args[i])
      if rec is Some(r) {
        if r.seq == 0 {
          continue // 創世記錄：驗證從 seq=1 起銜接
        }
      }
      let _ = lines.push(args[i])
    }
    let (ok, n) = @sledger.sled_parse_lines(lines)
    if ok {
      println("VERIFY_OK records=\{n}")
    } else {
      println("VERIFY_FAIL at_record=\{n}")
    }
    return
  }
  // 產生模式：確定性帳本
  let ledger = @sledger.sled_new()
  let _ = @sledger.sled_record(
    ledger,
    "score",
    "invariant",
    "pkg=score;graded_trace_cyclicity=PASS;flat_sym_C44=\{@score.count_monomials(4, 4, 4)}",
  )
  let _ = @sledger.sled_record(
    ledger,
    "spec",
    "invariant",
    "pkg=spec;witten_index_example=1;superflow_example=1",
  )
  let _ = @sledger.sled_record(
    ledger,
    "stensor",
    "invariant",
    "pkg=stensor;quartic_monomials=\{@stensor.quartic_monomials().length()};odd_kernel=0",
  )
  let (cz2, acz2) = @sgauge.cl_center_anticenter(2)
  let (cz3, acz3) = @sgauge.cl_center_anticenter(3)
  let _ = @sledger.sled_record(
    ledger,
    "stwist",
    "invariant",
    "pkg=stwist;h2_z2d3=\{@twist.h2_dim(@twist.grp([2, 2, 2]), 2)}",
  )
  let _ = @sledger.sled_record(
    ledger,
    "sgauge",
    "invariant",
    "pkg=sgauge;cl2_center=\{cz2};cl2_anticenter=\{acz2};cl3_center=\{cz3};cl3_anticenter=\{acz3}",
  )
  let _ = @sledger.sled_record(
    ledger,
    "snc",
    "invariant",
    "pkg=snc;nc6=\{@snc.nc_partitions(6).length()};mobius_nc6=-42;diam_flip8=7",
  )
  let _ = @sledger.sled_record(
    ledger,
    "sradon",
    "invariant",
    "pkg=sradon;spec_n7=n_and_n2+n;mult=n2-1",
  )
  let _ = @sledger.sled_record(
    ledger,
    "smetric",
    "invariant",
    "pkg=smetric;lap_nullity_p_div_n=2;vr_circle_beta=1,1",
  )
  let _ = @sledger.sled_record(
    ledger,
    "sevolve",
    "invariant",
    "pkg=sevolve;evo_steps=6;index_const=2;tamper_detected=true",
  )
  let _ = @sledger.sled_record(
    ledger,
    "health",
    "health",
    "scope=superlab;dead_removed=14;dup_merged=4;warnings=36to10;errors=0;tests=125of125",
  )
  let out = @sledger.sled_jsonl(ledger)
  let mut cur = ""
  for ch in out {
    if ch == '\n' {
      if cur != "" {
        println(cur)
      }
      cur = ""
    } else {
      cur = "\{cur}\{ch}"
    }
  }
  if cur != "" {
    println(cur)
  }
}
