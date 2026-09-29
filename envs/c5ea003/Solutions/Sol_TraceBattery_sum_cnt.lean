-- Prove2me | solution 1 for TraceBattery.sum_cnt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T03:02:18.483245+00:00
-- url     : https://prove2.me/submissions/709196df-ccd0-40cd-bd01-69fdcb0160e0

/-
# `TraceBattery.sum_cnt`
Target `d0a2967b-d110-4a55-b2c4-f0b2d93ca974` (Open, not deprecated at submission time).

An ORDINARY PROOF, not a reduction: nothing is imported from `Theorems`, so `#print axioms solution`
carries no `sorryAx` and needs no axiom-audit module.

The claim is the fibre-partition count. `img f` is `univ.image f`, the attained readings, and
`cnt f a` is `(univ.filter (f · = a)).card`, the size of the fibre over `a`. Summing fibre sizes
over the attained values recovers the whole population, which is exactly Mathlib's
`Finset.card_eq_sum_card_fiberwise`; its side condition is that `f` maps `univ` into `img f`,
discharged by `Finset.mem_image_of_mem`.
-/
import Mathlib
import Definitions.Def_Speculative_AutoResearch_TraceBatteryEntropy

set_option autoImplicit false

open TraceBattery Finset in
/-- **The target, verbatim.** -/
theorem solution {Ω : Type*} [Fintype Ω] {α : Type*} (f : Ω → α) :
    ∑ a ∈ img f, cnt f a = Fintype.card Ω := by
  classical
  have hmem : ∀ x ∈ (Finset.univ : Finset Ω), f x ∈ img f := by
    intro x _
    simpa [TraceBattery.img] using Finset.mem_image_of_mem f (Finset.mem_univ x)
  have key := Finset.card_eq_sum_card_fiberwise hmem
  simpa [TraceBattery.cnt, TraceBattery.fib, Finset.card_univ] using key.symm
