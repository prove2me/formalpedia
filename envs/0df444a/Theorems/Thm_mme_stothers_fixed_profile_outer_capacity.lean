-- Prove2me | Theorems.Thm_mme_stothers_fixed_profile_outer_capacity
-- name    : mme_stothers_fixed_profile_outer_capacity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T19:39:31.635008+00:00
-- url     : https://prove2.me/theorems/05c85c56-04aa-4f50-b130-ea98f5ba0eba
-- title:
--   Fixed Stothers induced outer-family capacity
-- statement:
--   At every sufficiently large integer multiple of the exact rational Stothers profile, there is an induced, mode-disjoint family of exact outer addresses whose cardinality, multiplied by the exact product of the ten cyclic constituent rates, reaches the fixed global rate up to a uniform square-root-exponential loss. Explicitly, for some constant $C\ge0$, the family $F_m$ satisfies $$G(\tau)^{N_m}e^{-C\sqrt{N_m+1}}\le |F_m|\prod_{r=0}^9 v_r(\tau)^{n_r c_r(m)}.$$ The claim is scalar/combinatorial: it comprises the marginal multinomial estimate, maximum-entropy completion-degree control, affine Salem--Spencer hashing, collision pruning, and Stirling absorption, but contains no tensor-value substitution.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3, Equations (3.2)--(3.4), Lemma 5.2, and Equation (5.3); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_mme_stothers_fixed_outer_profile

open BigOperators Filter

set_option autoImplicit false

theorem mme_stothers_fixed_profile_outer_capacity
    (tau : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in Filter.atTop,
        ∃ F : Finset (MME.StothersFourth.FixedExactOuterAddress m),
          MME.StothersFourth.FixedInducedModeDisjoint F ∧
          (MME.StothersFourth.globalRate 6 tau
                MME.StothersFourth.fixedProfileB
                MME.StothersFourth.fixedProfileB) ^
                (MME.StothersFourth.fixedOuterLength m) *
              Real.exp
                (-C * Real.sqrt
                  (((MME.StothersFourth.fixedOuterLength m + 1 : ℕ) : ℝ))) ≤
            (F.card : ℝ) *
              (∏ r : Fin 10,
                (MME.StothersFourth.classValue 6 tau r) ^
                  (MME.StothersFourth.classMultiplicity r *
                    MME.StothersFourth.fixedProfileCount m r)) := by
  sorry
