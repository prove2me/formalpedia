-- Prove2me | Theorems.Thm_mme_dwz_prescribed_z_restriction_value_forget_profile_below
-- name    : mme_dwz_prescribed_z_restriction_value_forget_profile_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T16:06:43.505649+00:00
-- url     : https://prove2.me/theorems/85639775-2ccf-4b22-8422-f5bb1d3ebcc4
-- title:
--   A prescribed splitting certificate yields unrestricted six-symmetric value below its rate
-- statement:
--   Let a tensor T have a prescribed Z-split restriction certificate of rate V at exponent parameter tau. For every real W with 0≤W<V, the unrestricted tensor T has six-symmetrized tau-value at least W. The certificate supplies actual matrix-product restrictions at arbitrarily large compatible lengths; forgetting the Z restriction yields the standard public tau-value witnesses. The strict inequality W<V and the restriction-witness premise are essential to the stated bridge.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/abs/2210.10173, printed pp. 22-24, Definitions 3.7 and 3.9 and Equation (3); p. 72, Definition 8.1. Rational compatible-length finite-witness certificate form; no full limsup-equivalence assertion.

import Definitions.Def_mme_dwz_prescribed_z_split_value

set_option autoImplicit false

universe u

open MME MME.DWZRestrictedValue MME.DWZComponentRestriction Module BigOperators Filter

theorem mme_dwz_prescribed_z_restriction_value_forget_profile_below
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (tau V W : ℝ)
    (hW : 0 ≤ W) (hWV : W < V)
    (h : HasPrescribedZSixRestrictionValueAtLeast T bZ grade p tau V) :
    HasSixSymmetricTauValueAtLeast T tau W := by sorry
