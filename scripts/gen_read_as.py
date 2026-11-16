import argparse
import json
from pathlib import Path


def render():
    cases = json.loads(Path("data/read-as-cases.json").read_text())

    def flatten(node):
        if isinstance(node, str):
            return node
        return "".join(flatten(child) for child in node.get("children", []))

    for key, case in cases.items():
        if flatten(case["node"]) != case["text"]:
            raise ValueError(f"Source node and extracted text differ: {key}")
    out = [
        "module",
        "",
        "meta import Ritsuryo.Basis",
        "",
        "/-!",
        "# 読替え検査の原文データ",
        "",
        "`data/read-as-cases.json` の法令履歴ID付き原文を、文字を変えずに定義へ展開する。",
        "`scripts/gen_read_as.py` で生成する。入管法第13条第7項と第41条第1項、",
        "水産業協同組合法第34条の2第3項、第70条第3項、第92条第5項、第105条第5項。",
        "-/",
        "",
        "@[expose] public section",
        "",
        "namespace Ritsuryo.LegalText",
    ]
    for key, case in cases.items():
        parts = case["article"].split("_")
        article = f"第{parts[0]}条" + "".join(f"の{part}" for part in parts[1:])
        out += [
            "",
            f"/-- {case['revision']} {article}第{case['paragraph']}項の全文。 -/",
            f"@[ritsuryo_basis {json.dumps(case['law'], ensure_ascii=False)} "
            f'"{article}第{case["paragraph"]}項"]',
            f"def {key} : String :=",
        ]
        chunks = [case["text"][i : i + 65] for i in range(0, len(case["text"]), 65)]
        out += [
            "  "
            + json.dumps(chunk, ensure_ascii=False)
            + (" ++" if i < len(chunks) - 1 else "")
            for i, chunk in enumerate(chunks)
        ]
    values = {key: case["text"] for key, case in cases.items()}
    values.update(
        immigrationNeedle="三十日以内とする。但し、主任審査官は、やむを得ない事由があると認めるときは、三十日を限り延長することができる。",
        immigrationReplacement="第三章に規定する上陸の手続が完了するまでの間において、主任審査官が必要と認める期間とする。",
        kanjiBut="但し",
        kanaBut="ただし",
        fishInnerNeedle="前条第十項",
        fishInnerReplacement="前条第十項本文",
        fishOuterNeedle="前条第十項本文及び第十二項",
        fishOuterReplacement="前条第十項本文",
        fishExpected="３経営管理委員については、前条第十項本文の規定を準用する。この場合において、同条第十項中「三分の二」とあるのは、「四分の三」と読み替えるものとする。",
    )
    values["immigrationQuote"] = (
        "「"
        + values["immigrationNeedle"]
        + "」とあるのは「"
        + values["immigrationReplacement"]
        + "」"
    )
    values["fishOuterQuote"] = (
        "「前条第十項本文及び第十二項」とあるのは「前条第十項本文」"
    )
    values["fishInnerQuote"] = "「前条第十項」とあるのは、「前条第十項本文」"
    for key, value in values.items():
        out += [
            "",
            f"/-- `{key}` のUnicode符号位置列。原文との一致は生成器の検査で確認する。 -/",
            f"def {key}Tokens : List Nat := [",
        ]
        codes = [str(ord(char)) for char in value]
        out += [
            "  " + ", ".join(codes[i : i + 10]) + ("," if i + 10 < len(codes) else "]")
            for i in range(0, len(codes), 10)
        ]
    return "\n".join(out + ["", "end Ritsuryo.LegalText", ""])


parser = argparse.ArgumentParser()
parser.add_argument("--check", action="store_true")
args = parser.parse_args()
target = Path("Ritsuryo/LegalText/Data.lean")
output = render()
if args.check:
    if target.read_text() != output:
        raise SystemExit("Read-as data differs from the source fixture")
else:
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(output)
