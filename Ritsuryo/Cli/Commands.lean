module

public import Ritsuryo.Cli.Period
public import Ritsuryo.Cli.Tax

/-!
# コマンド表

`ritsuryo` のコマンド・サブコマンド・パラメータの定義をまとめた表。解析、`help`、`--generate-cli-skeleton`、
`--cli-input-json` の読み込みは、すべてこの表から導く。
-/

public section

namespace Ritsuryo.Cli

def commands : List Command :=
  periodCommands ++ taxCommands

end Ritsuryo.Cli
