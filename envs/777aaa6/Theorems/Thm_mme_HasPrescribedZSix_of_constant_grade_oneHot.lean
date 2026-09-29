-- Prove2me | Theorems.Thm_mme_HasPrescribedZSix_of_constant_grade_oneHot
-- name    : mme_HasPrescribedZSix_of_constant_grade_oneHot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T08:00:35.466191+00:00
-- url     : https://prove2.me/theorems/2395316a-e9f3-4a87-a679-920eba292fc6
-- title:
--   Ordinary six-symmetric value survives a forced one-hot Z split
-- statement:
--   Let $T$ be an order-three tensor over a field, and let its distinguished $Z$ basis have constant grade $a_0$. Let $p$ be an integer split profile of denominator $D>0$ whose entire count $D$ lies at $a_0$. For real $\tau$ and $V\ge0$, an ordinary six-symmetric restriction-value certificate of value $V$ for $T$ implies the same value certificate for the exact prescribed-$Z$ sequence $T^{\otimes Dm}[p]$.
--
--   In particular, for every $0<v<V$ and every cutoff there is a compatible length $n=Dm$ beyond the cutoff and an actual matrix-multiplication direct-sum restriction of the six-symmetrization satisfying
--
--   $$v^{6n}\le\sum_i(a_i b_i c_i)^\tau.$$
--
--   Thus a split already forced by the canonical basis causes no loss of asymptotic value. The conclusion is a restriction certificate, which is stronger than merely postulating an entropy bound or a degeneration certificate.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5, Definitions 3.7, 3.9, and 8.1. Formalization corollary for a forced constant-grade split; not a separately numbered theorem in the paper.

import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME MME.DWZRestrictedValue Module

universe u

set_option autoImplicit false

theorem mme_HasPrescribedZSix_of_constant_grade_oneHot
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Type u} {t : ℕ} (bZ : Basis ι K (T.V 2))
    (grade : ι → Fin t) (p : IntegerZSplitProfile t) (a0 : Fin t)
    (hgrade : ∀ x, grade x = a0)
    (hone : ∀ a, p.count a = if a = a0 then p.denominator else 0)
    (tau V : ℝ) (hV : 0 ≤ V)
    (hSix : HasSixSymmetricTauValueAtLeast T tau V) :
    HasPrescribedZSixRestrictionValueAtLeast T bZ grade p tau V := by sorry
