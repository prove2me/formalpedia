-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.isSquare_square_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:55:54.219694+00:00
-- url     : https://prove2.me/submissions/5a478940-0941-4e66-9987-3b9857c11f80

import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace ErdosProblems.Erdos243.PaperCompleteR11
end ErdosProblems.Erdos243.PaperCompleteR11

/-!
# The algebraic descent after a good Frobenius prime is supplied

No prime-existence theorem is declared here. The ordinary number-field
specialisation argument, its finite exceptional set, and the missing formal
Chebotarev dependency are stated explicitly in analytic_proofs.md.
-/

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution {K : Type*} [Field K]
    (c γ : K) (hc : c ≠ 0) : IsSquare (c ^ 2 * γ) ↔ IsSquare γ := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s / c, ?_⟩
    apply (mul_left_cancel₀ (pow_ne_zero 2 hc))
    calc
      c ^ 2 * γ = s * s := hs
      _ = c ^ 2 * ((s / c) * (s / c)) := by field_simp
  · rintro ⟨s, hs⟩
    refine ⟨c * s, ?_⟩
    rw [hs]
    ring
