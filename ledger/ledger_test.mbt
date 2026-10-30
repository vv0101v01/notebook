///|
fn rows_radon() -> Array[Array[Int32]] {
  @evolve.rowset_rows(@evolve.evolve_radon(2, 10007, 5, 7331))
}

///|
/// [T-Ledger-Det] 同一串操作 ⇒ 同一個 tip；`replay` 重建得到相同賬本。
test "ledger is deterministic and replayable" {
  let rows = rows_radon()
  let mut a = @ledger.empty()
  for r in rows {
    a = @ledger.observe(a, r)
  }
  let b = @ledger.replay(rows)
  assert_eq(@ledger.ledger_tip(a), @ledger.ledger_tip(b))
  assert_eq(@ledger.ledger_len(a), rows.length())
  assert_eq(@ledger.verify(a), true)
  assert_eq(@ledger.verify(b), true)
}

///|
/// [T-Ledger-Persist] append 是持久操作：舊快照的 tip、長度、可驗證性全部不變。
test "append is persistent: old snapshots stay valid" {
  let mut l = @ledger.empty()
  l = @ledger.observe(l, [1, 2, 3])
  l = @ledger.observe(l, [2, 4, 6])
  l = @ledger.observe(l, [3, 6, 9])
  let snapshot = l
  let tip0 = @ledger.ledger_tip(snapshot)
  let mut l2 = l
  l2 = @ledger.observe(l2, [4, 8, 12])
  l2 = @ledger.observe(l2, [5, 10, 15])
  // 舊快照不受影響
  assert_eq(@ledger.ledger_tip(snapshot), tip0)
  assert_eq(@ledger.ledger_len(snapshot), 3)
  assert_eq(@ledger.verify(snapshot), true)
  assert_eq(@ledger.ledger_len(l2), 5)
  // 新賬本以舊賬本為前綴
  assert_eq(@ledger.fork_index(snapshot, l2), 3)
}

///|
/// [T-Ledger-Fork] 分歧點 = 共同前綴長度（內容定址的 hash 比對）。
test "fork index is the common prefix length" {
  let a = @ledger.observe(
    @ledger.observe(@ledger.observe(@ledger.empty(), [1, 0]), [0, 1]),
    [1, 1],
  )
  let b = @ledger.observe(
    @ledger.observe(@ledger.observe(@ledger.empty(), [1, 0]), [0, 1]),
    [2, 2],
  )
  assert_eq(@ledger.fork_index(a, b), 2)
  let c = @ledger.observe(@ledger.observe(@ledger.empty(), [1, 0]), [0, 1])
  assert_eq(@ledger.fork_index(a, c), 2)
  assert_eq(@ledger.fork_index(a, a), 3)
}

///|
/// [T-Ledger-Tamper] 篡改任一條的 hash 都會被 verify 抓到。
test "tamper detection" {
  let rows = rows_radon()
  let l = @ledger.replay(rows)
  assert_eq(@ledger.verify(l), true)
  assert_eq(@ledger.verify(@ledger.corrupt(l, 0)), false)
  assert_eq(@ledger.verify(@ledger.corrupt(l, 1)), false)
  assert_eq(@ledger.verify(@ledger.corrupt(l, rows.length() - 1)), false)
}

///|
/// [T-Ledger-Audit] 導出的關係自帶父節點，可逐條重算驗證（proof-carrying）。
test "derived relations are auditable from their parents" {
  let l = @ledger.replay(rows_radon())
  let (l2, cnt) = @ledger.derive_into(l, 10007, false)
  assert_eq(cnt > 0, true)
  // evolve 的獨立計數必須一致（同一引擎、同一關係集）
  let rels = @evolve.derive_relations(
    @evolve.rowset_of(rows_radon()),
    10007,
    false,
  )
  assert_eq(cnt, rels.length())
  let (pass, fail_) = @ledger.audit(l2, 10007, false)
  assert_eq(pass, cnt)
  assert_eq(fail_, 0)
  let (n, obs, der, ok) = @ledger.stats(l2)
  assert_eq(n, obs + der)
  assert_eq(obs, @ledger.ledger_len(l))
  assert_eq(ok, true)
  assert_eq(@ledger.verify(l2), true)
}

///|
/// [Inv-Ledger] 賬本導出的關係在**每一個**觀測上成立（逐列檢查，而非只看 rank）。
test "every derived relation holds on every observation" {
  let rows = rows_radon()
  let l = @ledger.replay(rows)
  let (l2, cnt) = @ledger.derive_into(l, 10007, false)
  assert_eq(cnt > 0, true)
  let mut checks = 0
  for e in @ledger.entries(l2) {
    if e.kind == 1 {
      for r in rows {
        let lg = @evolve.rowset_of([r])
        assert_eq(@evolve.holds_mod(lg, e.values, 10007), true)
        checks = checks + 1
      }
    }
  }
  assert_eq(checks, cnt * rows.length())
}

///|
/// [E-Ledger-Bridge] evolve 的觀測列整批入賬：長度、可稽核、可重放，且與逐條 append 等價。
test "bridge: evolve RowSet ingests into the persistent ledger" {
  let rs = @evolve.evolve_radon(3, 10007, 6, 3)
  let rows = @evolve.rowset_rows(rs)
  let (l2, cnt) = @ledger.ingest_rowset(@ledger.empty(), rs, 0)
  assert_eq(cnt, rows.length())
  assert_eq(@ledger.ledger_len(l2), rows.length())
  assert_eq(@ledger.verify(l2), true)
  // 與逐條 append 的結果**完全一致**（同一條雜湊鏈）
  let (l3, _) = @ledger.ingest_rows(@ledger.empty(), rows, 0)
  assert_eq(@ledger.ledger_tip(l2), @ledger.ledger_tip(l3))
  // 重放同一批列得到同一個 tip
  let replay_l = @ledger.replay(@ledger.observation_rows(l2))
  assert_eq(@ledger.ledger_tip(replay_l), @ledger.ledger_tip(l2))
  // 追加不影響既有前綴
  let l4 = @ledger.append(l2, 2, [9], [])
  assert_eq(@ledger.fork_index(l2, l4), rows.length())
  // 由入賬的觀測導出恆定關係，再稽核：每條導出條目都要在它的父條目上成立
  let (l5, derived) = @ledger.derive_into(l4, 10007, false)
  assert_eq(derived > 0, true)
  let (checked, bad) = @ledger.audit(l5, 10007, false)
  assert_eq(checked, derived) // 每條導出條目在**它的全部父條目**上都成立才算通過
  assert_eq(bad, 0)
  assert_eq(@ledger.verify(l5), true)
}
