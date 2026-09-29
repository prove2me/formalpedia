-- Prove2me | Theorems.Thm_mme_dwz_prescribed_z_power_projection
-- name    : mme_dwz_prescribed_z_power_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T16:06:46.654941+00:00
-- url     : https://prove2.me/theorems/152a5f37-af45-4ed5-9b3c-cf0b270f1d20
-- title:
--   Prescribed Z-split powers are literal restrictions
-- statement:
--   For any order-three tensor with a basis-labelled Z partition and any positive-denominator integer split profile, its prescribed Z-split power at a compatible length is a restriction of the corresponding ordinary tensor power. This formalizes the zeroing-out operation in DWZ Definition 3.9 without duplicating the X or Y spaces.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/abs/2210.10173, printed pp. 22-24, Definitions 3.7 and 3.9 and Equation (3); p. 72, Definition 8.1. Rational compatible-length finite-witness certificate form; no full limsup-equivalence assertion.

import Definitions.Def_mme_dwz_prescribed_z_split_value

set_option autoImplicit false

universe u

open MME MME.DWZRestrictedValue MME.DWZComponentRestriction Module

theorem mme_dwz_prescribed_z_power_projection
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (m : ℕ) :
    TensorObj.Restrict (prescribedZPower T bZ grade p m) (T.kronPow (p.length m)) := by sorry
