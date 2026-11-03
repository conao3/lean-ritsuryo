module

public import Ritsuryo.Cli.Period
public import Ritsuryo.Cli.Tax

/-!
# コマンド表

`ritsuryo` のコマンド・サブコマンド・パラメータの定義をまとめた表。解析、`help`、`--generate-cli-skeleton`、
`--cli-input-json` の読み込みは、すべてこの表から導く。

表の各行は `Ritsuryo/Cli/Period.lean`（`period`・`age`・`holiday`・`deadline`）と
`Ritsuryo/Cli/Tax.lean`（税のコマンド）に書き、ここで 1 つにつなぐ。
-/

public section

namespace Ritsuryo.Cli

/-- `ritsuryo` のすべてのコマンド。`help` の一覧はこの順に並ぶ。 -/
def commands : List Command :=
  periodCommands ++ taxCommands

end Ritsuryo.Cli
