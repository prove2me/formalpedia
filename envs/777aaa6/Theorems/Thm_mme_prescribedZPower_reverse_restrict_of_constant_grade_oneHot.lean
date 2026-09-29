-- Prove2me | Theorems.Thm_mme_prescribedZPower_reverse_restrict_of_constant_grade_oneHot
-- name    : mme_prescribedZPower_reverse_restrict_of_constant_grade_oneHot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T07:49:50.32164+00:00
-- url     : https://prove2.me/theorems/d2127289-f065-449d-a479-a98907f4af73
-- title:
--   A constant-grade prescribed Z power recovers the full tensor power
-- statement:
--   Let $T$ be an order-three tensor over a field $K$, with a chosen basis $b_Z$ of its third mode and a finite grade map that takes the constant value $a_0$. Let $p$ be an integer split profile with positive denominator $D$, assigning count $D$ to $a_0$ and count zero to every other grade. For every nonnegative integer $m$, the full tensor power is a restriction of the exact prescribed-Z power:
--
--   $$
--   T^{\otimes Dm}\preceq T^{\otimes Dm}[p].
--   $$
--
--   Here $A\preceq B$ means that independent linear maps applied to the modes of $B$ produce $A$. Together with the defining projection in the other direction, this identifies the constant-grade prescribed tensor with the full tensor power in the restriction preorder. This removes a prescribed-splitting condition when the actual Z basis already has the required unique grade. The statement includes $m=0$ and does not assume a tensor-value bound.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S3.SS9, printed pp. 22–24, Definitions 3.7 and 3.9. Direct formalization lemma for the constant-grade specialization of Definition 3.9; this corollary is not separately numbered in the paper.

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_tensor_quotient

open MME MME.DWZRestrictedValue Module

universe u

set_option autoImplicit false

theorem mme_prescribedZPower_reverse_restrict_of_constant_grade_oneHot
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Type u} {t : ℕ} (bZ : Basis ι K (T.V 2))
    (grade : ι → Fin t) (p : IntegerZSplitProfile t) (a0 : Fin t)
    (hgrade : ∀ x, grade x = a0)
    (hone : ∀ a, p.count a = if a = a0 then p.denominator else 0)
    (m : ℕ) :
    TensorObj.Restrict (T.kronPow (p.length m))
      (prescribedZPower T bZ grade p m) := by sorry
