-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.cubic_profile_integer_clearing
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:45:27.428667+00:00
-- url     : https://prove2.me/submissions/55ab013f-e244-4890-a51d-2ca933062c6e

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Mathlib
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic

/-!
# From actual modular cubic roots to the exceptional-set density

Rational profile coefficients are cleared over the
integers before reduction. There is deliberately no ring homomorphism from
`ℚ` to `ZMod p`. The final theorem is conditional on an actual divergent family
of good primes; producing that family from a number-field nonsquare remains a
separate global obligation, not a premise silently claimed to have been proved.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11
open scoped BigOperators
end ErdosProblems.Erdos243.PaperCompleteR11

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution (κ η : ℚ) :
    ∃ q A B : ℤ, 0 < q ∧
      (∀ n : ℕ, (q : ℚ) *
        (κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η) =
        (A : ℚ) * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + (B : ℚ)) ∧
      (κ ≠ 0 → A ≠ 0) := by
  have hdκ : (κ.den : ℚ) ≠ 0 := ne_of_gt (by exact_mod_cast κ.den_pos)
  have hdη : (η.den : ℚ) ≠ 0 := ne_of_gt (by exact_mod_cast η.den_pos)
  have hκ : (κ.den : ℚ) * κ = (κ.num : ℚ) := by
    calc
      (κ.den : ℚ) * κ = (κ.den : ℚ) * ((κ.num : ℚ) / (κ.den : ℚ)) := by
        congr 1
        exact (Rat.num_div_den κ).symm
      _ = (κ.num : ℚ) := by field_simp [hdκ]
  have hη : (η.den : ℚ) * η = (η.num : ℚ) := by
    calc
      (η.den : ℚ) * η = (η.den : ℚ) * ((η.num : ℚ) / (η.den : ℚ)) := by
        congr 1
        exact (Rat.num_div_den η).symm
      _ = (η.num : ℚ) := by field_simp [hdη]
  refine ⟨(κ.den : ℤ) * (η.den : ℤ), κ.num * (η.den : ℤ),
    η.num * (κ.den : ℤ), ?_, ?_, ?_⟩
  · exact_mod_cast Nat.mul_pos κ.den_pos η.den_pos
  · intro n
    push_cast
    linear_combination
      (η.den : ℚ) * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) * hκ +
      (κ.den : ℚ) * hη
  · intro hk hA
    have hAq : (κ.num : ℚ) * (η.den : ℚ) = 0 := by exact_mod_cast hA
    have hn : (κ.num : ℚ) = 0 := (mul_eq_zero.mp hAq).resolve_right hdη
    have hz : (κ.den : ℚ) * κ = 0 := hκ.trans hn
    exact hk ((mul_eq_zero.mp hz).resolve_left hdκ)
