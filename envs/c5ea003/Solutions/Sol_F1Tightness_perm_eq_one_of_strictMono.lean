-- Prove2me | solution 1 for F1Tightness.perm_eq_one_of_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:11:50.71349+00:00
-- url     : https://prove2.me/submissions/67ee38d6-2872-4330-ba57-a44c38ae2eb0

-- Sol generated from Probability/F1TightnessUniqueness.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore

/-!
# Uniqueness of the optimal scan policy (paper 250)

`Probability.F1TightnessCore` shows that on an antitone profile the ascending
scan minimises the expected probe count, so its speed-up `S_asc = 1/Λ` is the
best realizable one and the master bound overshoots it by the factor `X`.  Here
we sharpen that statement: on a *strictly* front-loaded profile the ascending
scan is the **unique** minimiser, so the quantity `S_asc` compared with the
bound is not an artefact of a particular tie-breaking among optimal policies.

Main results.

* `perm_eq_one_of_strictMono` — a strictly monotone permutation of `Fin M` is
  the identity (hence a non-identity policy always has an inversion).
* `scanCost_lt_polCost` — strict rearrangement: every policy other than the
  ascending one is strictly more expensive on a strictly antitone profile.
* `polCost_eq_scanCost_iff` — the optimal policy is unique.
* `speedup_lt_Sasc` — consequently the ascending speed-up strictly dominates
  every other policy, and (with `F1Tightness.speedup_lt_bound`) still falls
  short of the master bound by the factor `X`.
-/

open Finset

open F1Tightness

variable {M : ℕ}







open F1Tightness in
theorem solution{σ : Equiv.Perm (Fin M)} (h : StrictMono σ) : σ = 1 := by
  have hinv : StrictMono (σ⁻¹ : Equiv.Perm (Fin M)) := by
    intro i j hij
    by_contra hcon
    push_neg at hcon
    have hmono := h.monotone hcon
    simp at hmono
    exact absurd hij (not_lt.mpr hmono)
  ext i
  have h1 : i ≤ σ i := h.le_apply
  have h2 : i ≤ (σ⁻¹ : Equiv.Perm (Fin M)) i := hinv.le_apply
  have h3 : σ i ≤ i := by
    have := h.monotone h2
    simpa using this
  simp [le_antisymm h3 h1]
