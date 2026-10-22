-- Prove2me | Theorems.Thm_YeIPA_Asymptotic_lemma_7_9
-- name    : YeIPA.Asymptotic.lemma_7_9
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:27.85854+00:00
-- url     : https://prove2.me/theorems/7c1658e0-d67c-4ca4-bd98-e2b0c0a11937
-- title:
--   Lemma 7.9 — for PSD M, M_PP x_P = 0 iff M_PPᵀ x_P = 0, and then (M_ZP + M_PZᵀ) x_P = 0
-- statement:
--   Let $M$ be a real square matrix that is positive semi-definite in the sense $v^TMv\ge0$ for all $v$ ($M$ need not be symmetric), partitioned as in (7.21):
--   $$M=\begin{pmatrix}M_{PP}&M_{PZ}\\ M_{ZP}&M_{ZZ}\end{pmatrix}.$$
--   Then for every $x_P$, $M_{PP}x_P=0$ if and only if $M_{PP}^Tx_P=0$. Furthermore, $M_{PP}x_P=0$ implies that $(M_{ZP}+M_{PZ}^T)x_P=0$.
--
--   The lemma is the linear-algebra step behind the least-squares characterization of the predictor direction for monotone LCPs (Lemma 7.11).
--
--   **Formalization Note** The index sets $P$ and $Z$ are arbitrary finite types and $M$ is the block matrix over their disjoint union, which is the book's "partitioned (following a re-ordering of rows and columns)". PSD is the book's non-symmetric notion $v^TMv\ge0$, not Mathlib's `PosSemidef` (which requires symmetry).
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 221, Lemma 7.9

import Mathlib

open Matrix

namespace YeIPA.Asymptotic

/-- Lemma 7.9 (p. 221). Let `M = (M_PP M_PZ; M_ZP M_ZZ)` be PSD in the book's sense
(`vᵀMv ≥ 0` for all `v`, `M` not necessarily symmetric), partitioned as in (7.21). Then
`M_PP x_P = 0` iff `M_PPᵀ x_P = 0`; and `M_PP x_P = 0` implies `(M_ZP + M_PZᵀ) x_P = 0`. -/
theorem lemma_7_9 {p z : Type*} [Fintype p] [Fintype z] [DecidableEq p] [DecidableEq z]
    (MPP : Matrix p p ℝ) (MPZ : Matrix p z ℝ) (MZP : Matrix z p ℝ) (MZZ : Matrix z z ℝ)
    (hM : ∀ v : p ⊕ z → ℝ, 0 ≤ v ⬝ᵥ (Matrix.fromBlocks MPP MPZ MZP MZZ *ᵥ v))
    (xP : p → ℝ) :
    (MPP *ᵥ xP = 0 ↔ MPPᵀ *ᵥ xP = 0) ∧
      (MPP *ᵥ xP = 0 → (MZP + MPZᵀ) *ᵥ xP = 0) := by sorry

end YeIPA.Asymptotic
