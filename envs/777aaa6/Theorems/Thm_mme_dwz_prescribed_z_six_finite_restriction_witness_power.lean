-- Prove2me | Theorems.Thm_mme_dwz_prescribed_z_six_finite_restriction_witness_power
-- name    : mme_dwz_prescribed_z_six_finite_restriction_witness_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T06:59:11.402227+00:00
-- url     : https://prove2.me/theorems/44d219ae-c221-4d57-9477-742f3faca083
-- title:
--   Prescribed-Z six-symmetric finite witnesses power without weight loss
-- statement:
--   Fix an order-three tensor over an arbitrary field, a basis-labelled Z grading, and an integer split profile $p$ of positive denominator $D$. Let $P_p(m)$ be its prescribed-Z tensor at length $Dm$. Suppose an actual finite direct sum of matrix-multiplication tensors restricts from $\operatorname{sym}_6(P_p(m))$ and has total $\tau$-weight at least $v^{6Dm}$. Then for every nonnegative integer $r$ there is an actual finite direct sum restricting from $\operatorname{sym}_6(P_p(mr))$ with total weight at least
--
--   $$v^{6Dmr}.$$
--
--   This holds for every real $v$ and $\tau$, includes zero indices and zero repetitions, and retains the full finite matrix-multiplication extraction. It does not assume the repeated witness or a shared witness length.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/abs/2210.10173v5, Definitions 3.7 and 3.9 (printed pp. 22–23) and Equation (3) (printed p. 24). Exact finite repetition of the restriction-witness normalization of Equation (3), using the established lossless MM direct-sum power flattening; no limsup-equivalence assertion.

import Definitions.Def_mme_dwz_prescribed_z_split_value

set_option autoImplicit false

universe u

open MME MME.DWZRestrictedValue MME.DWZComponentRestriction Module

theorem mme_dwz_prescribed_z_six_finite_restriction_witness_power
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (m r : ℕ) (tau v : ℝ)
    (h : SixFiniteWitness TensorObj.Restrict
      (prescribedZPower T bZ grade p m) (p.length m) tau v) :
    SixFiniteWitness TensorObj.Restrict
      (prescribedZPower T bZ grade p (m * r)) (p.length (m * r)) tau v := by sorry
