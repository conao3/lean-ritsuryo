module

meta import Ritsuryo.Basis

/-!
# 祝日の表の型

内閣府の「国民の祝日」CSV（`data/syukujitsu.csv`）の 1 行を表す型を置く。CSV の各行は
`scripts/gen_holidays.py` が `Ritsuryo/Holiday/Data/Generated.lean` の年ごとの表 `Data.y1955` ... に変換し、
年の順に並べた `Data.byYear` から引く。

行の種類は名称で分ける。名称が「休日」の行は第3条第2項（振替休日）か第3条第3項（国民の休日）で、
それ以外の行（「休日（祝日扱い）」と特例法による休日を含む）は第3条を当てはめるときに「国民の祝日」として扱う
（`docs/interpretation.md`）。
-/

@[expose] public section

namespace Ritsuryo.Holiday

/-- CSV の行の種類。 -/
inductive EntryKind where
  /-- 第2条の国民の祝日 -/
  | national
  /-- 名称が「休日（祝日扱い）」の行 -/
  | treatedAsNational
  /-- 特例法による休日（結婚の儀、大喪の礼、即位礼正殿の儀） -/
  | specialLaw
  /-- 名称が「休日」の行。第3条第2項・第3項による休日 -/
  | rest
  deriving DecidableEq, Repr, Inhabited

/-- CSV の 1 行。年は年ごとの表の側で持ち、月・日・名称・種類を持つ。 -/
structure Entry where
  month : Nat
  day : Nat
  name : String
  kind : EntryKind
  deriving DecidableEq, Repr, Inhabited

end Ritsuryo.Holiday
