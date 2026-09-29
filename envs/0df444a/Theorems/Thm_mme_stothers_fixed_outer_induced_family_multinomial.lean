-- Prove2me | Theorems.Thm_mme_stothers_fixed_outer_induced_family_multinomial
-- name    : mme_stothers_fixed_outer_induced_family_multinomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:02:08.878266+00:00
-- url     : https://prove2.me/theorems/0749ea1a-88ac-4219-8c44-88879f3f75dc
-- title:
--   Induced family retaining the fixed Stothers marginal multinomial
-- statement:
--   Let $N_m = 3 s m$, where $s=97{,}942{,}072$ is the denominator of the fixed Stothers profile, and let $A_0,…,A_8$ be its exact integer marginal counts. Write $M_m=N_m!/((mA_0)!⋯(mA_8)!)$ for the associated multinomial coefficient. There is a constant $C≥0$ such that, for every sufficiently large $m$, one can select an induced, coordinate-disjoint family $F_m$ of exact-profile fourth-power addresses satisfying
--
--   $$M_m e^{-C √(N_m+1)} ≤ |F_m|.$$
--
--   This is the precise combinatorial extraction needed by the fixed-profile outer laser. It isolates affine hashing, progression-free-set selection, maximum-entropy completion control, and collision pruning from the already formalized scalar and tensor-value arguments.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Equations (3.3)--(3.4), specialized to the exact stationary profile in Section 5.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Multinomial
import Definitions.Def_mme_stothers_fixed_outer_profile

open BigOperators Filter

set_option autoImplicit false

theorem mme_stothers_fixed_outer_induced_family_multinomial :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in Filter.atTop,
        ∃ F : Finset (MME.StothersFourth.FixedExactOuterAddress m),
          MME.StothersFourth.FixedInducedModeDisjoint F ∧
          (Nat.multinomial Finset.univ
              (fun j : Fin 9 ↦
                MME.StothersFourth.fixedMarginalBaseCount j * m) : ℝ) *
            Real.exp
              (-C * Real.sqrt
                (((MME.StothersFourth.fixedOuterLength m + 1 : ℕ) : ℝ))) ≤
              (F.card : ℝ) := by
  sorry
