-- Prove2me | solution 1 for Round10.factorFromTrace_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:41:30.360776+00:00
-- url     : https://prove2.me/submissions/8d427f32-1c8f-47ce-9699-716071affab8

-- Sol generated from Geometry/Round10Closures/HintAmplification.lean
import Mathlib
import Definitions.Def_Geometry_Round10Closures_HintAmplification
import Definitions.Def_Geometry_Round10Closures_JointClosure
/-
Round-10 Closures — Part V: pricing the hint (HINT-AMP scope restatement).

The round-10 batch flagged hint amplification (Coppersmith, partial key exposure) as the
one resource the barrier framework never priced, because it is not extraction from `N`
alone: it consumes an *external* hint.  This file makes the scope restatement precise in
the simplest possible model of a hint — the trace `p + q` of the factorisation — and proves
that this single hint is amplified to the full factorisation by an explicit, closed-form,
constant-time extractor:

    factorFromTrace N s = (s - sqrt (s² - 4N)) / 2 .

Contrast with `JointClosure.no_profile_extractor`, where no extractor whatsoever exists for
the hint-free free-witness channel: the two theorems together delimit the framework's
scope, "extraction from `N` alone" versus "amplification of hints".
-/

open Round10






open Round10 in
theorem solution{p q : ℕ} (hpq : p ≤ q) : factorFromTrace (p * q) (p + q) = p := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
  have hs : p + (p + d) = 2 * p + d := by ring
  have hsqrt : Nat.sqrt ((2 * p + d) * (2 * p + d) - 4 * (p * (p + d))) = d := by
    have h : (2 * p + d) * (2 * p + d) = 4 * (p * (p + d)) + d * d := by ring
    rw [h]
    simp
  rw [factorFromTrace, hs, hsqrt]
  omega
