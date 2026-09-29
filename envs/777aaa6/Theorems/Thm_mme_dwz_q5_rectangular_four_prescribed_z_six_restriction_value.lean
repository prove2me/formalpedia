-- Prove2me | Theorems.Thm_mme_dwz_q5_rectangular_four_prescribed_z_six_restriction_value
-- name    : mme_dwz_q5_rectangular_four_prescribed_z_six_restriction_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T09:34:25.095903+00:00
-- url     : https://prove2.me/theorems/ed862109-b829-4d46-be55-bbbbdc62fc4d
-- title:
--   Four elementary q=5 prescribed-Z entropy value endpoints
-- statement:
--   Let $K$ be a field, $p=(p_0,p_1,p_2;d)$ an integer fine-$Z$ profile, and $\tau>0$. Write $H(p)=-\sum_a(p_a/d)\log(p_a/d)$, with $0\log0=0$. The actual canonical $q=5$ components $T_{013}$ and $T_{103}$, for $p_0=0$, and $T_{031}$ and $T_{301}$, for $p_2=0$, have prescribed-$Z$ six-symmetrized restriction value at least
--   \[e^{\tau H(p)}5^\tau.\]
--   The certificate supplies arbitrarily large compatible finite restrictions for every positive strict lower base. It uses each tensor's literal canonical Z basis and preserves the exact profile.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/html/2210.10173v5, Definition 3.9 and Section 7.3 after Lemma 7.14, elementary boundary prescribed-Z components. The numerical specialization uses the exact published q=5 ledger profiles; the paper's entropy asymptotic is implemented as explicit arbitrarily-large finite restriction witnesses.

import Theorems.Thm_mme_dwz_q5_rectangular_four_prescribed_z_finite_restrictions
import Theorems.Thm_mme_dwz_q5_odd_coarse_prescribed_z_word_card
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_sixSymmetrization_MMObj_isomorphic
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_modern_entropy_data
import Mathlib.Tactic

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue Module
open scoped BigOperators
universe u
set_option autoImplicit false

theorem mme_dwz_q5_rectangular_four_prescribed_z_six_restriction_value (K : Type u) [Field K] (p : IntegerZSplitProfile 3)
    (tau : ℝ) (htau : 0 < tau) :
    let V := Real.exp (tau * ∑ a : Fin 3, Real.negMulLog
      ((p.count a : ℝ) / p.denominator)) * (5 : ℝ) ^ tau
    (p.count 0 = 0 →
      HasPrescribedZSixRestrictionValueAtLeast
        ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 0 1 3))
        ((coarseClassBasis (K := K) 5 2 3).reindex Equiv.ulift.symm)
        LiftedCoarsePair.leftGrade p tau V) ∧
    (p.count 2 = 0 →
      HasPrescribedZSixRestrictionValueAtLeast
        ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 0 3 1))
        ((coarseClassBasis (K := K) 5 2 1).reindex Equiv.ulift.symm)
        LiftedCoarsePair.leftGrade p tau V) ∧
    (p.count 0 = 0 →
      HasPrescribedZSixRestrictionValueAtLeast
        ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 1 0 3))
        ((coarseClassBasis (K := K) 5 2 3).reindex Equiv.ulift.symm)
        LiftedCoarsePair.leftGrade p tau V) ∧
    (p.count 2 = 0 →
      HasPrescribedZSixRestrictionValueAtLeast
        ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 3 0 1))
        ((coarseClassBasis (K := K) 5 2 1).reindex Equiv.ulift.symm)
        LiftedCoarsePair.leftGrade p tau V) := by sorry
