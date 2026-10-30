// ledger：超級持久賬本（structurally persistent, content-addressed, proof-carrying）
//
// [D-PLedger] 賬本是一條**不可變**的單向鏈：append 回傳新賬本並共享舊前綴（O(1)、結構共享），
//   因此任何時刻取得的舊快照永遠有效 —— 這就是「持久（persistent）」在資料結構上的意思，
//   而「超級」指的是：**每條導出的關係都自帶它的父條目，可被重算驗證**（proof-carrying）。
// [D-Hash] 內容定址：FNV-1a 64 位。hash 由 (seq, kind, values, parents, prev) 決定，
//   任何一個位元組被改動都會使後續所有 hash 失效。
// [T-Ledger-Det] 同一串操作 ⇒ 同一個 tip（純函式，無隱藏狀態）。
// [T-Ledger-Persist] append 不改變舊快照的 tip 與可驗證性。
// [T-Ledger-Fork] 兩條賬本的分歧點 = 共同前綴長度（由 hash 逐條比對得出）。
// [T-Ledger-Audit] 每條導出條目都能由其父條目重算通過（定理的「可攜證明」）。
// [T-Ledger-Tamper] 篡改任一 hash 會使 verify 失敗。

///|
/// [D-Entry] 賬本條目。`kind`：0 = 觀測，1 = 導出的關係，2 = 定理宣稱。
pub struct Entry {
  seq : Int32
  kind : Int32
  values : Array[Int32]
  parents : Array[Int32]
  prev : Int64
  hash : Int64
}

///|
/// [D-Cell] 單向鏈的節點（不可變）。
pub enum Cell {
  Nil
  Node(Entry, Cell)
}

///|
/// [D-Ledger] 賬本頭：鏈首、長度、tip hash。
pub struct Ledger {
  head : Cell
  len : Int32
  tip : Int64
}

///|
/// [D-Fnv] FNV-1a 64 位元（一個 Int32 餵入）。
pub fn fnv1a(seed : Int64, x : Int32) -> Int64 {
  let h = seed ^ (x.to_int64() & 4294967295L)
  h * 1099511628211L
}

///|
pub fn hash_values(seed : Int64, xs : Array[Int32]) -> Int64 {
  let mut h = seed
  for x in xs {
    h = fnv1a(h, x)
  }
  h
}

///|
/// [D-HashEntry] 條目的內容 hash。
pub fn hash_entry(e : Entry) -> Int64 {
  let mut h = fnv1a(2166136261L, e.seq)
  h = fnv1a(h, e.kind)
  h = hash_values(h, e.values)
  h = fnv1a(h, 0)
  h = hash_values(h, e.parents)
  h = fnv1a(h, 1)
  h = h ^ e.prev
  h
}

///|
pub fn empty() -> Ledger {
  Ledger::{ head: Nil, len: 0, tip: 2166136261L, }
}

///|
/// [E-Append] O(1) 的持久 append：新節點指向舊鏈首，舊賬本完全不受影響。
pub fn append(
  l : Ledger,
  kind : Int32,
  values : Array[Int32],
  parents : Array[Int32],
) -> Ledger {
  let draft = Entry::{
    seq: l.len,
    kind,
    values,
    parents,
    prev: l.tip,
    hash: 0L,
  }
  let e = Entry::{ ..draft, hash: hash_entry(draft), }
  Ledger::{ head: Node(e, l.head), len: l.len + 1, tip: e.hash, }
}

///|
/// 追加一條觀測（無父節點，但自動記錄「全部既有觀測」為隱含上下文：不存，靠 seq 定位）。
pub fn observe(l : Ledger, values : Array[Int32]) -> Ledger {
  append(l, 0, values, [])
}

///|
/// 追加一條導出關係，父節點 = 參與導出的觀測 seq 列表。
pub fn append_derived(
  l : Ledger,
  values : Array[Int32],
  parents : Array[Int32],
) -> Ledger {
  append(l, 1, values, parents)
}

///|
pub fn ledger_len(l : Ledger) -> Int32 {
  l.len
}

///|
pub fn ledger_tip(l : Ledger) -> Int64 {
  l.tip
}

///|
/// [E-At] 取第 seq 條（鏈由新到舊，故以反向索引走訪）。
pub fn entry_at(l : Ledger, seq : Int32) -> Entry? {
  let mut cur = l.head
  let mut found : Entry? = None
  let mut go = true
  while go {
    match cur {
      Nil => go = false
      Node(e, rest) =>
        if e.seq == seq {
          found = Some(e)
          go = false
        } else {
          cur = rest
        }
    }
  }
  found
}

///|
/// [E-Entries] 由舊到新列出全部條目。
pub fn entries(l : Ledger) -> Array[Entry] {
  let rev : Array[Entry] = []
  let mut cur = l.head
  let mut go = true
  while go {
    match cur {
      Nil => go = false
      Node(e, rest) => {
        rev.push(e)
        cur = rest
      }
    }
  }
  let out : Array[Entry] = []
  let mut i = rev.length() - 1
  while i >= 0 {
    out.push(rev[i])
    i = i - 1
  }
  out
}

///|
/// [T-Ledger-Det] 完整重算並檢查：seq 連續、prev 連結、hash 相符。
pub fn verify(l : Ledger) -> Bool {
  let es = entries(l)
  if es.length() != l.len {
    return false
  }
  let mut prev_tip = 2166136261L
  let mut ok = true
  for i = 0; i < es.length(); i = i + 1 {
    let e = es[i]
    if e.seq != i || e.prev != prev_tip || e.hash != hash_entry(e) {
      ok = false
    }
    prev_tip = e.hash
  }
  if prev_tip != l.tip {
    ok = false
  }
  ok
}

///|
/// [T-Ledger-Fork] 兩條賬本的共同前綴長度（以 hash 逐條比對；內容相同即 hash 相同）。
pub fn fork_index(a : Ledger, b : Ledger) -> Int32 {
  let ea = entries(a)
  let eb = entries(b)
  let n = if ea.length() < eb.length() { ea.length() } else { eb.length() }
  let mut i = 0
  while i < n {
    if ea[i].hash != eb[i].hash {
      return i
    }
    i = i + 1
  }
  i
}

///|
/// [E-Corrupt] 刻意破壞第 seq 條的 hash（用於驗證「篡改必被抓」）。
pub fn corrupt(l : Ledger, seq : Int32) -> Ledger {
  let es = entries(l)
  let out : Array[Entry] = []
  for e in es {
    if e.seq == seq {
      let bad = Entry::{ ..e, hash: e.hash ^ 1L, }
      out.push(bad)
    } else {
      out.push(e)
    }
  }
  from_entries(out)
}

///|
/// [D-FromEntries] 由條目陣列重建賬本（保留條目自身的 hash，故可造出「壞」賬本）。
pub fn from_entries(es : Array[Entry]) -> Ledger {
  let mut head : Cell = Nil
  let mut tip = 2166136261L
  let mut n = 0
  for i = 0; i < es.length(); i = i + 1 {
    head = Node(es[i], head)
    tip = es[i].hash
    n = n + 1
  }
  Ledger::{ head, len: n, tip, }
}

///|
/// [E-Rows] 取出全部**觀測**條目的列（餵給消元引擎）。
pub fn observation_rows(l : Ledger) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for e in entries(l) {
    if e.kind == 0 {
      out.push(e.values)
    }
  }
  out
}

///|
/// [E-DeriveInto] 由既有觀測用消元導出恆定關係，並把它們寫成新的導出條目（帶父節點）。
///   回傳 (新賬本, 導出條數)。
pub fn derive_into(l : Ledger, p : Int32, exact : Bool) -> (Ledger, Int32) {
  let rows = observation_rows(l)
  if rows.length() < 2 {
    return (l, 0)
  }
  let parents : Array[Int32] = []
  for e in entries(l) {
    if e.kind == 0 {
      parents.push(e.seq)
    }
  }
  let rels = @evolve.derive_relations(@evolve.rowset_of(rows), p, exact)
  let mut out = l
  let mut cnt = 0
  for r in rels {
    out = append_derived(out, r, parents)
    cnt = cnt + 1
  }
  (out, cnt)
}

///|
/// [T-Ledger-Audit] 稽核：每條導出條目是否真的在它的所有父條目上成立。
///   回傳 (通過數, 失敗數)。
pub fn audit(l : Ledger, p : Int32, exact : Bool) -> (Int32, Int32) {
  let es = entries(l)
  let mut passed = 0
  let mut failed = 0
  for e in es {
    if e.kind == 1 {
      let mut ok = true
      for ps in e.parents {
        match entry_at(l, ps) {
          Some(parent) => {
            let lg = @evolve.rowset_of([parent.values])
            let holds = if exact {
              @evolve.holds_exact(lg, e.values)
            } else {
              @evolve.holds_mod(lg, e.values, p)
            }
            if !holds {
              ok = false
            }
          }
          None => ok = false
        }
      }
      if ok {
        passed = passed + 1
      } else {
        failed = failed + 1
      }
    }
  }
  (passed, failed)
}

///|
/// [E-Replay] 由同一串觀測重建賬本，必須得到同一個 tip（[T-Ledger-Det] 的計算版本）。
pub fn replay(rows : Array[Array[Int32]]) -> Ledger {
  let mut l = empty()
  for r in rows {
    l = observe(l, r)
  }
  l
}

///|
/// [D-Stats] 賬本摘要：(長度, 觀測數, 導出數, 是否可驗證)。
pub fn stats(l : Ledger) -> (Int32, Int32, Int32, Bool) {
  let mut obs = 0
  let mut der = 0
  for e in entries(l) {
    if e.kind == 0 {
      obs = obs + 1
    } else if e.kind == 1 {
      der = der + 1
    }
  }
  (l.len, obs, der, verify(l))
}

///|
/// [E-Ledger-Bridge] 把一批係數列（例如 evolve 的 RowSet，或 relations 的 rec_values）
///   整批灌進持久賬本：每列一條記錄。
///   回傳 (新賬本, 寫入條數)。這是「觀測 → 賬本」的單一入口，避免各處重複拼 append。
pub fn ingest_rows(
  l : Ledger,
  rows : Array[Array[Int32]],
  kind : Int32,
) -> (Ledger, Int32) {
  let mut out = l
  let mut cnt = 0
  for r in rows {
    out = append(out, kind, r, [])
    cnt = cnt + 1
  }
  (out, cnt)
}

///|
/// [E-Ledger-Bridge] 直接把 evolve 的 RowSet 灌進賬本（經 ingest_rows）。
pub fn ingest_rowset(
  l : Ledger,
  rs : @evolve.RowSet,
  kind : Int32,
) -> (Ledger, Int32) {
  ingest_rows(l, @evolve.rowset_rows(rs), kind)
}
