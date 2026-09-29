-- Prove2me | Theorems.Thm_mme_stothers_general_outer_hash_budget_of_degree_data
-- name    : mme_stothers_general_outer_hash_budget_of_degree_data
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T17:22:49.899157+00:00
-- url     : https://prove2.me/theorems/87cb6bb0-0302-4ce6-901a-6d1c80f1a6e7
-- title:
--   Outer hash budget from degree data
-- statement:
--   **From degree data to a good hash state, eventually, at any profile.**
--
--   Fix a strictly positive integral ten-class profile $\beta$. Suppose that for all large scales $m$
--   the following *degree data* holds, with $N = 3Dm$, $V = N!/\prod_j M_j!$ and
--   $D_* = \prod_j M_j!/\prod_\sigma T_\sigma!$:
--
--   - the exact-profile targets number exactly $V D_*$, and $D_*\ge1$;
--   - every completion star, in every mode, has at most $D = (6(N+1))^{100}D_*$ members;
--   - $D \le 5^{1000N}$.
--
--   Then for all large $m$ there is a vertex-closed family $E$ of marginal-supported addresses with
--
--   $$\#\{\text{target--ambient collisions in }E\} + V\,e^{-10^{6}\sqrt{N+1}} \;\le\;
--   \#\{\text{targets in }E\}.$$
--
--   This packages the whole outer affine hash behind a purely arithmetic interface: the caller supplies
--   counting facts about the profile, and receives a single retained family with more targets than
--   collisions, up to a loss that is exponentially small in $\sqrt N$ and therefore invisible in the
--   laser limit. Internally the exponential ceiling on $D$ is what allows a Behrend-type choice of odd
--   prime modulus and progression-free residue set with the margin the averaging argument needs.
--
--   Note that the parameter selection itself is profile-independent -- it depends only on $N$ and $D_*$
--   -- so the only profile-specific inputs are the three counting facts above.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Lemma 3.3; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.NatCast

open MME BigOperators Filter

set_option autoImplicit false

theorem mme_stothers_general_outer_hash_budget_of_degree_data
    (base : Fin 10 → ℕ) (hbase : ∀ r, 0 < base r)
    (hdata : ∀ᶠ m : ℕ in atTop,
      let N := MME.StothersFourth.genOuterLength base m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9, ((MME.StothersFourth.genMarginalCount base m j).factorial : ℝ)
      let Dstar : ℕ :=
        (∏ j : Fin 9, (MME.StothersFourth.genMarginalCount base m j).factorial) /
          ∏ sigma : {sigma : Fin 3 → Fin 9 //
              (∑ s, (sigma s).val) = 8},
            (MME.StothersFourth.genJointMultiplicity base m sigma.1).factorial
      let P := (6 * (N + 1)) ^ 100
      let D := P * Dstar
      (Nat.card
          {a : MME.StothersFourth.GenMarginalSupportedAddress base m //
            MME.StothersFourth.GenHasExactJointProfile a} : ℝ) = V * (Dstar : ℝ) ∧
        1 ≤ Dstar ∧
        (∀ i : Fin 3,
          ∀ a : {a : MME.StothersFourth.GenMarginalSupportedAddress base m //
            MME.StothersFourth.GenHasExactJointProfile a},
          Nat.card
            {b : MME.StothersFourth.GenMarginalSupportedAddress base m //
              b.1 i = a.1.1 i} ≤ D) ∧
        D ≤ 5 ^ (1000 * N)) :
    ∀ᶠ m : ℕ in atTop,
      let N := MME.StothersFourth.genOuterLength base m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9, ((MME.StothersFourth.genMarginalCount base m j).factorial : ℝ)
      ∃ E : Finset (MME.StothersFourth.GenMarginalSupportedAddress base m),
        MME.StothersFourth.GenMarginalVertexClosed E ∧
        ((MME.StothersFourth.genTargetAmbientCollisions E).card : ℝ) +
            V * Real.exp
              (-1000000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          ((MME.StothersFourth.genExactTargetEdges E).card : ℝ) := by
  sorry
