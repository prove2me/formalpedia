-- Prove2me | Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_outer_hash_budget_of_degree_data
-- name    : MME.StothersFourth.mme_stothers_fixed_outer_hash_budget_of_degree_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:40:32.459615+00:00
-- url     : https://prove2.me/theorems/b17c53f2-9f1e-4859-ac58-52466d75f583
-- title:
--   Fixed Stothers affine-hash budget from enumerative degree data
-- statement:
--   Assume the fixed exact-profile target family has cardinality $VD_*$, its target completion factor is positive, each target-centered completion star has degree at most $D=(6(N+1))^{100}D_*$, and $D\le5^{1000N}$ for all sufficiently large scales. Then the affine Salem--Spencer hash construction produces a vertex-closed retained family $E$ satisfying
--
--   $$
--   C(E)+V\exp\!\left(-10^6\sqrt{N+1}\right)\le T(E).
--   $$
--
--   This theorem isolates the reusable hashing and deterministic selection step from the profile-specific entropy and multinomial estimates.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Equations (3.3)--(3.4), https://www.maths.ed.ac.uk/~sandy/a11164.pdf. The proof uses the standard affine Salem--Spencer hash, bounded collision degree, and averaging over hash states.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.NatCast
import Definitions.Def_mme_stothers_fixed_outer_profile

open MME BigOperators Filter

set_option autoImplicit false

theorem MME.StothersFourth.mme_stothers_fixed_outer_hash_budget_of_degree_data
    (hdata : ∀ᶠ m : ℕ in Filter.atTop,
      let N := MME.StothersFourth.fixedOuterLength m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9, ((MME.StothersFourth.fixedMarginalCount m j).factorial : ℝ)
      let Dstar : ℕ :=
        (∏ j : Fin 9, (MME.StothersFourth.fixedMarginalCount m j).factorial) /
          ∏ sigma : {sigma : Fin 3 → Fin 9 //
              (∑ s, (sigma s).val) = 8},
            (MME.StothersFourth.fixedJointMultiplicity m sigma.1).factorial
      let P := (6 * (N + 1)) ^ 100
      let D := P * Dstar
      (Nat.card
          {a : MME.StothersFourth.FixedMarginalSupportedAddress m //
            MME.StothersFourth.FixedHasExactJointProfile a} : ℝ) = V * (Dstar : ℝ) ∧
        1 ≤ Dstar ∧
        (∀ i : Fin 3,
          ∀ a : {a : MME.StothersFourth.FixedMarginalSupportedAddress m //
            MME.StothersFourth.FixedHasExactJointProfile a},
          Nat.card
            {b : MME.StothersFourth.FixedMarginalSupportedAddress m //
              b.1 i = a.1.1 i} ≤ D) ∧
        D ≤ 5 ^ (1000 * N)) :
    ∀ᶠ m : ℕ in Filter.atTop,
      let N := MME.StothersFourth.fixedOuterLength m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9, ((MME.StothersFourth.fixedMarginalCount m j).factorial : ℝ)
      ∃ E : Finset (MME.StothersFourth.FixedMarginalSupportedAddress m),
        MME.StothersFourth.FixedMarginalVertexClosed E ∧
        ((MME.StothersFourth.fixedTargetAmbientCollisions E).card : ℝ) +
            V * Real.exp
              (-1000000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          ((MME.StothersFourth.fixedExactTargetEdges E).card : ℝ) := by
  sorry
