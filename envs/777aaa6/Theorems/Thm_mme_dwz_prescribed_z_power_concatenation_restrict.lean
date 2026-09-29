-- Prove2me | Theorems.Thm_mme_dwz_prescribed_z_power_concatenation_restrict
-- name    : mme_dwz_prescribed_z_power_concatenation_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T06:33:19.96384+00:00
-- url     : https://prove2.me/theorems/0844ed73-f692-4bb2-9f91-5df213fdfc53
-- title:
--   Prescribed Z-split powers concatenate by literal restriction
-- statement:
--   Let $T$ be an order-three tensor over an arbitrary field, with a basis-labelled grading of its Z space. Let $p$ be a prescribed integer split profile of positive denominator $D$, and write $P_p(m)$ for the literal Z-only restriction of $T^{\otimes Dm}$ that retains precisely the words containing $p_a m$ letters of each grade $a$. For every pair of nonnegative integers $m,n$,
--
--   $$P_p(m)\otimes P_p(n)\preceq P_p(m+n).$$
--
--   Here $\preceq$ is actual tensor restriction, with modewise linear maps, rather than an inequality of numerical values. The theorem includes either segment having length zero and does not duplicate the X or Y spaces.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/abs/2210.10173v5, Definition 3.7 (printed pp. 22–23) and Definition 3.9 (printed p. 23). This is the finite concatenation consequence of the exact marginal-count definition; it does not assert the nested-limsup equivalence or asymptotic multiplicativity.

import Definitions.Def_mme_dwz_prescribed_z_split_value

set_option autoImplicit false

universe u

open MME MME.DWZRestrictedValue MME.DWZComponentRestriction Module

theorem mme_dwz_prescribed_z_power_concatenation_restrict
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (m n : ℕ) :
    TensorObj.Restrict
      (TensorObj.kron (prescribedZPower T bZ grade p m)
        (prescribedZPower T bZ grade p n))
      (prescribedZPower T bZ grade p (m + n)) := by sorry
