module

@[expose] public section

namespace Ritsuryo

structure Law where
  name : String
  lawId : String
  lawNum : String
  deriving Inhabited, Repr

def laws : List Law := [
  ⟨"民法", "129AC0000000089", "明治二十九年法律第八十九号"⟩,
  ⟨"年齢計算ニ関スル法律", "135AC1000000050", "明治三十五年法律第五十号"⟩,
  ⟨"国税通則法", "337AC0000000066", "昭和三十七年法律第六十六号"⟩,
  ⟨"国税通則法施行令", "337CO0000000135", "昭和三十七年政令第百三十五号"⟩,
  ⟨"民事訴訟法", "408AC0000000109", "平成八年法律第百九号"⟩,
  ⟨"国民の祝日に関する法律", "323AC1000000178", "昭和二十三年法律第百七十八号"⟩,
  ⟨"天皇の即位の日及び即位礼正殿の儀の行われる日を休日とする法律", "430AC0000000099",
    "平成三十年法律第九十九号"⟩,
  ⟨"改暦ノ布告", "105DF0000000337", "明治五年太政官布告第三百三十七号"⟩,
  ⟨"閏年ニ関スル件", "131IO0000000090", "明治三十一年勅令第九十号"⟩
]

def Law.find? (name : String) : Option Law :=
  laws.find? (·.name == name)

end Ritsuryo
