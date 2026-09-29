-- Prove2me | solution 1 for AlmostLossless.setMass_univ
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T03:19:07.457819+00:00
-- url     : https://prove2.me/submissions/8cd0d645-5ef3-4a50-a680-82c6f20879f4

/-
# `AlmostLossless.setMass_univ`
Target `0041f06e` (Open, not deprecated at draft time; re-read live immediately before submitting).

An ORDINARY PROOF: nothing is imported from `Theorems`, so `#print axioms solution` carries no
`sorryAx` and no axiom-audit module is needed.

`setMass μ S` is `∑ x ∈ S, μ.mass x`, and a `FinProbDist` carries the field
`mass_sum_one : ∑ x : α, mass x = 1`. Since `∑ x : α` is notation for the sum over `Finset.univ`,
the goal IS that field.

BINDERS: copied from the platform's own expected type, not inferred —
  {α : Type*} [Fintype α] (μ : NonArchInfoTheory.FinProbDist α)
There is NO `[DecidableEq α]`. Seven prior submissions by another user were rejected for carrying
exactly that spurious instance; the mathematics was never the obstacle.
-/
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_MinEntropy

set_option autoImplicit false

open AlmostLossless NonArchInfoTheory in
/-- **The target, verbatim.** -/
theorem solution {α : Type*} [Fintype α] (μ : NonArchInfoTheory.FinProbDist α) :
    AlmostLossless.setMass μ Finset.univ = 1 := by
  first
  | exact μ.mass_sum_one
  | · unfold AlmostLossless.setMass
      exact μ.mass_sum_one
  | simp [AlmostLossless.setMass, μ.mass_sum_one]
