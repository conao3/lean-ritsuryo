import Ritsuryo.Tax.BasicDeduction2025

/-!
# 令和7年分の基礎控除と本体所得税の探索

0円から25,000,001円まで、隣り合う所得額を1円刻みで比較する。
各行は所得額、控除額、税額、所得1円増後の税額、税引後所得の減少額。
探索の対象は総所得と合計所得が同じ居住者で、他の所得控除と税額控除は0。
復興特別所得税、住民税、社会保険料を加える前の本体所得税だけを表示する。
-/

open Ritsuryo.Tax.BasicDeduction2025

def main : IO Unit := do
  IO.println "income,deduction,tax_before,tax_after,net_loss"
  for income in [0:25000001] do
    if largeJump income then
      let before := tax income 0
      let after := tax (income + 1) 0
      IO.println s!"{income},{spec income},{before},{after},{after - before - 1}"
