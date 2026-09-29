-- Prove2me | Theorems.Thm_MatrixCompletion_NoSpuriousMin_alignment_exists
-- name    : MatrixCompletion.NoSpuriousMin.alignment_exists
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T14:12:14.683655+00:00
-- url     : https://prove2.me/theorems/5bf80d09-b78a-46d7-8fba-5c8b3099205a
-- title:
--   Existence of an aligned exact factor: $UU^\top=ZZ^\top$ with $X^\top U\succeq 0$ (Chen–Li §4.2.1)
-- statement:
--   For every $X\in\mathbb{R}^{d\times r}$ and every target factor $Z$, there exists an exact factor $U$ of the ground truth — $UU^\top=ZZ^\top$ — that is *aligned* with $X$: the cross matrix $X^\top U$ is symmetric positive semidefinite.
--
--   Because factors of $ZZ^\top$ are determined only up to rotation, the error direction $\Delta = X-U$ is meaningful only after fixing the rotation; the aligned choice (equivalently, the minimizer of $\|X-ZR\|_F$ over orthogonal $R$, realized via the SVD $X^\top Z=ADB^\top$, $U=ZBA^\top$) is what makes $\Delta$ an effective direction of improvement in the Ge–Jin–Zheng framework. The positive semidefiniteness of $X^\top U = U^\top X$ is exactly what later yields $\langle\Delta^\top\Delta,(U+\Delta)^\top U\rangle\ge 0$ in the superlevel-set argument.
-- source:
--   Chen, Li 2019, Model-free Nonconvex Matrix Completion: Local Minima Analysis and Applications in Memory-efficient Kernel PCA, JMLR 20(142), https://arxiv.org/abs/1711.01742 (v3) [THE canonical reference: all milestones follow its Section 4], p. 19, Section 4.2.1 (U := U_r R with R := BA^T from the SVD X^T U_r = ADB^T; X^T U is psd and R is the Procrustes optimum). Provenance: Ge, Jin, Zheng 2017, No Spurious Local Minima in Nonconvex Low Rank Problems, https://arxiv.org/abs/1704.00708, Definition 6; Chen, Wainwright 2015, arXiv:1509.03025.

import Definitions.Def_MCNoSpuriousMinModel
import Mathlib.LinearAlgebra.Matrix.PosDef
open Matrix MatrixCompletion.NoSpuriousMin

theorem MatrixCompletion.NoSpuriousMin.alignment_exists
    {d r : ℕ} (Z X : Matrix (Fin d) (Fin r) ℝ) :
    ∃ U : Matrix (Fin d) (Fin r) ℝ, U * Uᵀ = Z * Zᵀ ∧ (Xᵀ * U).PosSemidef := by sorry
