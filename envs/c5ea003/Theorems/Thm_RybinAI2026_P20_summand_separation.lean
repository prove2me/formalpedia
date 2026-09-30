-- Prove2me | Theorems.Thm_RybinAI2026_P20_summand_separation
-- name    : RybinAI2026.P20.summand_separation
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-05T00:15:15.050866+00:00
-- url     : https://prove2.me/theorems/ffe49e09-36b6-4bfa-9d74-5ccf0003ecae
-- title:
--   Summand separation from transpose injectivity
-- statement:
--   Let $R$ be a commutative semiring with identity, let $n\ge 2$, and let $A=(a_{ij})$ be an $n\times n$ matrix. Assume that $x\mapsto A^T x$ is injective. If vectors $x,y\in R^n$ satisfy $Ax=Ay$, then every matrix summand agrees separately:
--
--   $$a_{pq}x_q=a_{pq}y_q\qquad\text{for all rows }p\text{ and columns }q.$$
--
--   This is the unital specialization of the source's summand separation lemma. Together with one-column separation, it yields transpose symmetry of injectivity over arbitrary commutative semirings with identity.
-- source:
--   Sixuan Gu, Wei Qi, Yaoyu Cheng, Transpose Symmetry of Injectivity over Commutative Semirings, arXiv:2608.16205v1 (2026), Section 3, Lemma 3 (Summand separation), equations (3.1)-(3.8). https://arxiv.org/html/2608.16205v1

import Mathlib.Data.Matrix.Mul

theorem RybinAI2026.P20.summand_separation
    {R : Type*} [CommSemiring R] {n : Nat} (hn : 2 <= n)
    (A : Matrix (Fin n) (Fin n) R)
    (hA : Function.Injective A.transpose.mulVec)
    (x y : Fin n -> R) (hxy : A.mulVec x = A.mulVec y) :
    forall p q, A p q * x q = A p q * y q := by sorry
