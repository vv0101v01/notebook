#!/bin/sh
# superledger.sh —— 跨執行持久帳本（shell 層；MoonBit 端見 sledger / cmd/superledger）
#
# 用法：
#   sh ledger/superledger.sh append    # 產生本次執行的記錄並去重追加，隨後全鏈驗證
#   sh ledger/superledger.sh verify    # 只驗證 LEDGER.jsonl
#   sh ledger/superledger.sh show      # 印出帳本
#
# 設計：wasm 目標無 fs API，故「寫檔」由 shell 完成；
#       帳本格式、sha256 雜湊鏈、驗證全在 MoonBit（sledger 套件）內實作。
set -e
cd "$(dirname "$0")/.."
LEDGER=ledger/LEDGER.jsonl
mkdir -p ledger

gen() { moon run cmd/superledger 2>/dev/null; }

case "${1:-verify}" in
  append)
    gen > /tmp/sled_new.jsonl
    touch "$LEDGER"
    # 去重追加：以整行為鍵（雜湊鏈使行內容唯一）
    while IFS= read -r line; do
      [ -z "$line" ] && continue
      if ! grep -qxF "$line" "$LEDGER"; then
        printf '%s\n' "$line" >> "$LEDGER"
      fi
    done < /tmp/sled_new.jsonl
    ;;
  show)
    cat "$LEDGER"
    exit 0
    ;;
esac

# 驗證（把帳本行餵回 MoonBit 驗證器）
if [ ! -s "$LEDGER" ]; then
  echo "LEDGER_EMPTY"
  exit 1
fi
# xargs 需要處理大量參數；行數 ≤ 64 時安全
moon run cmd/superledger -- --verify $(cat "$LEDGER")
