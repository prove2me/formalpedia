-- Prove2me | Theorems.Thm_YeIPA_Asymptotic_lemma_7_10
-- name    : YeIPA.Asymptotic.lemma_7_10
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:30.055787+00:00
-- url     : https://prove2.me/theorems/cf7191fe-7262-4149-9c03-4db1917c631f
-- title:
--   Lemma 7.10 — for PSD M, R(M_PP M_PZ; 0 I) = R(M_PPᵀ M_ZPᵀ; 0 −I)
-- statement:
--   Let $M$ be a real square matrix that is positive semi-definite in the sense $v^TMv\ge0$ for all $v$, partitioned as in (7.21), $M=\begin{pmatrix}M_{PP}&M_{PZ}\\ M_{ZP}&M_{ZZ}\end{pmatrix}$. Then
--   $$\mathcal R\begin{pmatrix}M_{PP}&M_{PZ}\\ 0&I\end{pmatrix}=\mathcal R\begin{pmatrix}M_{PP}^T&M_{ZP}^T\\ 0&-I\end{pmatrix},$$
--   where $\mathcal R(\cdot)$ is the range (column space) of a matrix.
--
--   It is used, with Lemma 7.9, to verify the optimality conditions of the least-squares problem (7.24) for monotone LCPs.
--
--   **Formalization Note** $P$ and $Z$ are arbitrary finite types; both block matrices are square, indexed by $P\sqcup Z$, with $0$ the zero $Z\times P$ block and $I$ the identity on $Z$. The range is `LinearMap.range` of the matrix acting on column vectors. PSD is the book's non-symmetric notion.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 221, Lemma 7.10

import Mathlib

open Matrix

namespace YeIPA.Asymptotic

/-- Lemma 7.10 (p. 221). Let `M = (M_PP M_PZ; M_ZP M_ZZ)` be PSD in the book's sense
(`vᵀMv ≥ 0` for all `v`), partitioned as in (7.21). Then the ranges (column spaces) agree:
`R(M_PP M_PZ; 0 I) = R(M_PPᵀ M_ZPᵀ; 0 −I)`. -/
theorem lemma_7_10 {p z : Type*} [Fintype p] [Fintype z] [DecidableEq p] [DecidableEq z]
    (MPP : Matrix p p ℝ) (MPZ : Matrix p z ℝ) (MZP : Matrix z p ℝ) (MZZ : Matrix z z ℝ)
    (hM : ∀ v : p ⊕ z → ℝ, 0 ≤ v ⬝ᵥ (Matrix.fromBlocks MPP MPZ MZP MZZ *ᵥ v)) :
    LinearMap.range (Matrix.fromBlocks MPP MPZ (0 : Matrix z p ℝ) (1 : Matrix z z ℝ)).mulVecLin =
      LinearMap.range
        (Matrix.fromBlocks MPPᵀ MZPᵀ (0 : Matrix z p ℝ) (-1 : Matrix z z ℝ)).mulVecLin := by sorry

end YeIPA.Asymptotic
