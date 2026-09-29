-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.lowerDensityAtLeast_of_linear_bound
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:48:41.699206+00:00
-- url     : https://prove2.me/submissions/c2f9efe5-990a-46c1-b302-6d6ebff6c126

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Mathlib
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Window incidences and quantitative exceptional density

Every hit is charged to an exceptional index together
with its offset. Overlapping windows therefore cost at most their length, not
the number of residue classes. No density assumption is hidden in the counting
lemmas. `LowerDensityAtLeast` uses the usual epsilon / eventual-prefix definition
of a lower bound for the lower asymptotic density (prefixes start at zero).
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11
open ErdosProblems.Erdos243.PaperCompleteR9
end ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution (E : Set ℕ) (a b c : ℝ)
    (hb : 0 < b)
    (h : ∀ X : ℕ, a * (X : ℝ) ≤ b * (exceptionCount E X : ℝ) + c) :
    LowerDensityAtLeast E (a / b) := by
  intro ε hε
  have hbε : 0 < b * ε := mul_pos hb hε
  obtain ⟨N, hN⟩ := exists_nat_gt (c / (b * ε))
  refine ⟨N, ?_⟩
  intro X hNX
  have hNX' : (N : ℝ) ≤ (X : ℝ) := by exact_mod_cast hNX
  have hcN : c < (N : ℝ) * (b * ε) := (div_lt_iff₀ hbε).mp hN
  have hcX : c ≤ (b * ε) * (X : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hNX' (le_of_lt hbε)
    nlinarith
  have hX := h X
  have hab : b * (a / b) = a := by field_simp [ne_of_gt hb]
  apply le_of_mul_le_mul_left (a := b) (b := (a / b - ε) * (X : ℝ))
      (c := exceptionCount E X) (by
    calc
    b * ((a / b - ε) * (X : ℝ)) = a * (X : ℝ) - (b * ε) * (X : ℝ) := by
      rw [← mul_assoc, mul_sub, hab]
      ring
    _ ≤ b * (exceptionCount E X : ℝ) := by linarith
    ) hb
