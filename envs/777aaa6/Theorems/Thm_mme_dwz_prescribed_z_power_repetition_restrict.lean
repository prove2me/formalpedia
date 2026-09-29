-- Prove2me | Theorems.Thm_mme_dwz_prescribed_z_power_repetition_restrict
-- name    : mme_dwz_prescribed_z_power_repetition_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T06:47:16.65621+00:00
-- url     : https://prove2.me/theorems/0a35debf-a700-4d5c-b8cd-991a049bdc5c
-- title:
--   Prescribed Z-split powers repeat by literal restriction
-- statement:
--   Let $T$ be an order-three tensor over an arbitrary field, equipped with a basis-labelled Z grading and a positive-denominator integer split profile $p$. Write $P_p(m)$ for the literal prescribed-Z restriction of the power of length $p.\mathrm{denominator}\,m$. For all nonnegative integers $m,r$,
--
--   $$P_p(m)^{\otimes r}\preceq P_p(mr).$$
--
--   The relation is actual tensor restriction. The statement includes $r=0$ and $m=0$, with a genuine proof of the tensor-unit case, and introduces no numerical value or common-witness hypothesis.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/abs/2210.10173v5, Definition 3.7 (printed pp. 22–23) and Definition 3.9 (printed p. 23). Finite repetition consequence of prescribed-Z concatenation; a structural ingredient for synchronizing finite witnesses, not an asymptotic-value or limsup-equivalence theorem.

import Definitions.Def_mme_dwz_prescribed_z_split_value

set_option autoImplicit false

universe u

open MME MME.DWZRestrictedValue MME.DWZComponentRestriction Module

theorem mme_dwz_prescribed_z_power_repetition_restrict
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (m r : ℕ) :
    TensorObj.Restrict ((prescribedZPower T bZ grade p m).kronPow r)
      (prescribedZPower T bZ grade p (m * r)) := by sorry
