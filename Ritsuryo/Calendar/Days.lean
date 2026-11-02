module

public import Ritsuryo.Calendar.Date
meta import Ritsuryo.Basis

@[expose] public section

namespace Ritsuryo

namespace Date

@[ritsuryo_basis "改暦ノ布告" "本則"]
def marchYear (d : Date) : Int :=
  if d.month ≤ 2 then d.year - 1 else d.year

@[ritsuryo_basis "改暦ノ布告" "本則"]
def marchMonth (m : Nat) : Int :=
  if m ≤ 2 then (m : Int) + 9 else (m : Int) - 3

@[ritsuryo_basis "改暦ノ布告" "本則"]
def monthStart (mp : Int) : Int :=
  (153 * mp + 2) / 5

@[ritsuryo_basis "閏年ニ関スル件" "本則"]
def yearStart (yoe : Int) : Int :=
  365 * yoe + yoe / 4 - yoe / 100

@[ritsuryo_basis "閏年ニ関スル件" "本則"]
def marchYearStart (y : Int) : Int :=
  (y / 400) * 146097 + yearStart (y % 400)

@[ritsuryo_basis "改暦ノ布告" "本則"]
def toDays (d : Date) : Int :=
  marchYearStart (marchYear d) + monthStart (marchMonth d.month) + d.day - 1 - 719468

@[ritsuryo_basis "閏年ニ関スル件" "本則"]
def centOf (doe : Int) : Int :=
  min (doe / 36524) 3

@[ritsuryo_basis "閏年ニ関スル件" "本則"]
def quadOf (doe : Int) : Int :=
  (doe - 36524 * centOf doe) / 1461

@[ritsuryo_basis "閏年ニ関スル件" "本則"]
def yrOf (doe : Int) : Int :=
  min ((doe - 36524 * centOf doe) % 1461 / 365) 3

@[ritsuryo_basis "閏年ニ関スル件" "本則"]
def yoeOf (doe : Int) : Int :=
  100 * centOf doe + 4 * quadOf doe + yrOf doe

@[ritsuryo_basis "改暦ノ布告" "本則"]
def monthOf (doy : Int) : Int :=
  (5 * doy + 2) / 153

@[ritsuryo_basis "改暦ノ布告" "本則"]
def ofDays (z : Int) : Date :=
  let z' := z + 719468
  let era := z' / 146097
  let doe := z' % 146097
  let yoe := yoeOf doe
  let doy := doe - yearStart yoe
  let mp := monthOf doy
  let day := doy - monthStart mp + 1
  let month := if mp < 10 then mp + 3 else mp - 9
  ⟨era * 400 + yoe + (if mp < 10 then 0 else 1), month.toNat, day.toNat⟩

end Date

end Ritsuryo
