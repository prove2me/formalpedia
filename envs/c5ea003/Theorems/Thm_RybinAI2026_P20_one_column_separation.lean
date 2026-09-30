-- Prove2me | Theorems.Thm_RybinAI2026_P20_one_column_separation
-- name    : RybinAI2026.P20.one_column_separation
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-05T00:15:11.476223+00:00
-- url     : https://prove2.me/theorems/962d1485-3062-4538-9d6b-2a9632d96eda
-- title:
--   One-column separation from transpose injectivity
-- statement:
--   Let $R$ be a commutative semiring with identity, let $n\ge 2$, and let $A=(a_{ij})$ be an $n\times n$ matrix. Assume that $x\mapsto A^T x$ is injective. For a fixed column $q$ and scalars $r,s\in R$, suppose
--
--   $$a_{iq}r=a_{iq}s\qquad\text{for every row }i.$$
--
--   Then
--
--   $$r=s.$$
--
--   This is the unital specialization of the source's one-column separation lemma. It converts equalities after multiplication by every entry of a single column into equality of the original scalars, without assuming additive cancellation.
-- source:
--   Sixuan Gu, Wei Qi, Yaoyu Cheng, Transpose Symmetry of Injectivity over Commutative Semirings, arXiv:2608.16205v1 (2026), Section 4, Lemma 5 (One-column separation), equations (4.1)-(4.5). https://arxiv.org/html/2608.16205v1

import Mathlib.Data.Matrix.Mul

theorem RybinAI2026.P20.one_column_separation
    {R : Type*} [CommSemiring R] {n : Nat} (hn : 2 <= n)
    (A : Matrix (Fin n) (Fin n) R)
    (hA : Function.Injective A.transpose.mulVec)
    (q : Fin n) (r s : R)
    (hcol : forall i, A i q * r = A i q * s) :
    r = s := by sorry
