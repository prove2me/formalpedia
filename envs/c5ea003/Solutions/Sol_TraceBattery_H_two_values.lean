-- Prove2me | solution 1 for TraceBattery.H_two_values
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T00:54:36.435055+00:00
-- url     : https://prove2.me/submissions/ae5222c9-ddd2-471f-9de3-68e7605185a7

/-
# `TraceBattery.H_two_values`
Target `81098356-b145-4d3c-ba7b-aa27c375571c` (recorded Open by the platform at submission time).

## How this is proved
By reduction to the platform node `WhichFactorWall.H_two_values`
(`55171b66-3ee1-4651-ab48-bc5ac90c1380`), which the platform records as Proved.

The two statements read identically but are NOT the same proposition as written: each namespace
declares its own population layer. `TraceBattery.img/cnt/H` are declared with `open Classical`,
while `WhichFactorWall.img/cnt/H` take a `[DecidableEq α]` instance. The bridge below shows the
two layers agree — membership-wise, so no instance juggling is needed — and then transports the
Proved statement across:

* `img_eq` : `TraceBattery.img f = WhichFactorWall.img f`   (`univ.image f` is `Finset.image f univ`)
* `cnt_eq` : `TraceBattery.cnt f a = WhichFactorWall.cnt f a` (both are `(univ.filter (f · = a)).card`)
* `H_eq`   : the two entropies agree, by rewriting the summand and the index set.

## Disclosures
The imported node is the only external fact used; it enters through the platform's `Theorems`
mirror and is not reproduced, so `#print axioms solution` reports `sorryAx` from that mirror alone.
The bridge lemmas are our own and are fully proved.
-/
import Mathlib
import Definitions.Def_Speculative_AutoResearch_TraceBatteryEntropy
import Theorems.Thm_WhichFactorWall_H_two_values

set_option autoImplicit false

namespace TBBridge

variable {Ω : Type*} [Fintype Ω] {α : Type*} [DecidableEq α]

theorem img_eq (f : Ω → α) : TraceBattery.img f = WhichFactorWall.img f := by
  ext a
  simp [TraceBattery.img, WhichFactorWall.img]

theorem cnt_eq (f : Ω → α) (a : α) : TraceBattery.cnt f a = WhichFactorWall.cnt f a := by
  unfold TraceBattery.cnt TraceBattery.fib WhichFactorWall.cnt
  congr 1
  ext w
  simp

theorem H_eq (f : Ω → α) : TraceBattery.H f = WhichFactorWall.H f := by
  unfold TraceBattery.H WhichFactorWall.H
  rw [img_eq f]
  exact Finset.sum_congr rfl (fun a _ => by rw [cnt_eq f a])

end TBBridge

open TraceBattery Classical in
/-- **The target, verbatim.** Bridged reduction to the Proved node `55171b66`.
Binders match the live target exactly: it sits under `open Classical in` and therefore takes NO
`[DecidableEq α]` argument, so decidability is manufactured inside the proof instead. -/
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] {α : Type*}
    (f : Ω → α) {a b : α} (hab : a ≠ b) (himg : img f = {a, b}) :
    H f = Real.binEntropy ((cnt f a : ℝ) / (Fintype.card Ω : ℝ)) := by
  classical
  rw [TBBridge.H_eq f, TBBridge.cnt_eq f a]
  exact WhichFactorWall.H_two_values f hab (by rw [← TBBridge.img_eq f]; exact himg)
