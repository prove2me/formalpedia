-- Prove2me | Theorems.Thm_mme_stothers_fixed_profile_fourth_value_of_capacity_and_blocks
-- name    : mme_stothers_fixed_profile_fourth_value_of_capacity_and_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T19:39:11.436278+00:00
-- url     : https://prove2.me/theorems/c7cd4029-34e8-406b-82f1-64b34b499138
-- title:
--   Assemble a fixed Stothers outer capacity and exact-block values
-- statement:
--   For the exact rational Stothers profile, suppose (i) the literal fourth-power grading is supported only on triples whose grades sum to eight, (ii) for all sufficiently large exact scales there is an induced mode-disjoint family whose cardinality times the product of the ten cyclic constituent values dominates the global rate up to an exp(-C sqrt(N)) loss, and (iii) every exact address block attains every strict lower value below that constituent product. Then the literal fourth Coppersmith--Winograd power has tau-value at least every nonnegative base strictly below the fixed global rate. This theorem is the general assembly step: it leaves the combinatorial capacity estimate and the exact-block constituent extraction as explicit, noncircular premises.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3, Equation (3.4), Lemmas 5.1--5.2, and Theorem 5.3; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. The formal theorem isolates the standard induced-word zeroing and subexponential-loss closure common to these steps.

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_fixed_outer_profile

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem mme_stothers_fixed_profile_fourth_value_of_capacity_and_blocks
    {K : Type u} [Field K]
    (tau : ℝ)
    (hblockSupport : ∀ sigma : Fin 3 → Fin 9,
      (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockTensor sigma ≠ 0 →
        (∑ s, ((sigma s).val : ℕ)) = 8)
    (hcapacity : ∃ C : ℝ, 0 ≤ C ∧
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
                    MME.StothersFourth.fixedProfileCount m r)))
    (hblocks : ∀ (m : ℕ)
        (a : MME.StothersFourth.FixedExactOuterAddress m) (W : ℝ),
      0 ≤ W →
      W < (∏ r : Fin 10,
        (MME.StothersFourth.classValue 6 tau r) ^
          (MME.StothersFourth.classMultiplicity r *
            MME.StothersFourth.fixedProfileCount m r)) →
      HasTauValueAtLeast
        (gradedAddressBlock
          (MME.StothersFourth.cwFourthCanonicalGrading K 6) a.1)
        tau W) :
    ∀ V : ℝ, 0 ≤ V →
      V < MME.StothersFourth.globalRate 6 tau
        MME.StothersFourth.fixedProfileB
        MME.StothersFourth.fixedProfileB →
      HasTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 6) tau V := by
  sorry
