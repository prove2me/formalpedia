-- Prove2me | Theorems.Thm_mme_dwz_canonical022_prescribed_z_six_restriction_value_all_q
-- name    : mme_dwz_canonical022_prescribed_z_six_restriction_value_all_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T08:38:13.868078+00:00
-- url     : https://prove2.me/theorems/0fbb6c15-c151-48d6-84ea-a12dc0a77bcc
-- title:
--   Prescribed-Z endpoints for canonical 022 components at every positive q
-- statement:
--   Let $K$ be a field, $q\ge1$ an integer, $p=(p_0,p_1,p_2;d)$ an integer profile with $d>0$ and $p_0+p_1+p_2=d$, and $\tau>0$. Write $\pi_a=p_a/d$ and $H(\pi)=-\sum_a\pi_a\log\pi_a$. With its canonical coarse-grade-$2$ $Z$ basis and left fine grade, the literal canonical component $T_{022}(q)$ satisfies
--
--   $$V^{(6),\mathrm{restr}}_\tau(T_{022}(q),p)\ge\exp(\tau H(\pi))\,q^{2\tau\pi_1}.$$
--
--   Every strict positive lower base has genuine finite direct-sum matrix-multiplication restriction witnesses at arbitrarily large compatible indices and physical lengths. This applies in particular to $q=5$ and $q=6$. It is a component endpoint, not a new numerical fourth-power certificate or final bound on the matrix-multiplication exponent.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/html/2210.10173v5, Section 6.3. Parameter generalization of the accepted canonical 022 prescribed-Z value theorem, using the already proved finite restriction cafeafd9-0247-4024-8865-8ee09f237295. This all-positive-q component endpoint is not separately numbered in the paper.

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_cw_square_restricted_central_power_words
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_modern_entropy_data

open MME MME.DWZFineChannel MME.DWZComponentRestriction MME.DWZRestrictedValue Module
universe u
set_option autoImplicit false

theorem mme_dwz_canonical022_prescribed_z_six_restriction_value_all_q
    (K : Type u) [Field K] (q : ℕ) (hq : 0 < q) (p : IntegerZSplitProfile 3)
    (tau : ℝ) (htau : 0 < tau) :
    let bZ : Basis (LiftedCoarsePair.{u} q 2) K ((Central022Block K q).V 2) :=
      (coarseClassBasis (K := K) q 2 2).reindex Equiv.ulift.symm
    HasPrescribedZSixRestrictionValueAtLeast (Central022Block K q) bZ
      LiftedCoarsePair.leftGrade p tau
      (Real.exp (tau * ∑ a : Fin 3, Real.negMulLog
          ((p.count a : ℝ) / p.denominator)) *
        (q : ℝ) ^ (2 * tau * (p.count 1 : ℝ) / p.denominator)) := by sorry
