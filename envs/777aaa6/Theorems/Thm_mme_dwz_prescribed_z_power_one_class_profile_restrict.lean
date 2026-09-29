-- Prove2me | Theorems.Thm_mme_dwz_prescribed_z_power_one_class_profile_restrict
-- name    : mme_dwz_prescribed_z_power_one_class_profile_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T16:55:28.648991+00:00
-- url     : https://prove2.me/theorems/1869dc8d-7943-43a5-9cb0-d469a9216655
-- title:
--   A one-class prescribed Z profile keeps the whole tensor power
-- statement:
--   Let $T$ be a tensor over a field $K$ with a chosen basis $b_Z$ of its third mode, and suppose the Z grade takes a **single** value, i.e. the grade map lands in a one-element type. Let $p$ be an integer Z-split profile on that one class, so $p$ has some denominator $D$ and its single count equals $D$.
--
--   Then the prescribed Z power is the whole tensor power:
--
--   $$T^{\otimes\, p.\mathrm{length}(m)} \;\trianglelefteq\; T^{[p]}_m .$$
--
--   Indeed every basis word of $T^{\otimes D m}$ has all $Dm$ of its letters in the one available class, so its left-grade histogram is automatically the prescribed one, $p.\mathrm{count}(0)\cdot m = Dm$; no word is filtered out and the projection is the identity.
--
--   This is the converse of the general projection `mme_dwz_prescribed_z_power_projection`, which holds only in this degenerate case. Its use is at a terminal node of a recursive prescribed-Z ledger: such a node carries a trivial one-class profile, and this lemma is what lets a plain tensor power be presented as that node's prescribed Z power.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue Module

universe u

set_option autoImplicit false

theorem mme_dwz_prescribed_z_power_one_class_profile_restrict
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin 1)
    (p : IntegerZSplitProfile 1) (m : ℕ) :
    TensorObj.Restrict (T.kronPow (p.length m))
      (prescribedZPower T bZ grade p m) := by sorry
