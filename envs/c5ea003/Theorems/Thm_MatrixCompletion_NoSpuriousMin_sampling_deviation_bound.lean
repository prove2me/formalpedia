-- Prove2me | Theorems.Thm_MatrixCompletion_NoSpuriousMin_sampling_deviation_bound
-- name    : MatrixCompletion.NoSpuriousMin.sampling_deviation_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-04T14:12:04.51362+00:00
-- url     : https://prove2.me/theorems/a7f0eab5-0078-43eb-a06b-381725e540d6
-- title:
--   Deterministic sampling-deviation bound $|D_{\Omega,t}(AC^\top,BD^\top)|\le\|\Omega-tJ\|\cdot(\text{row factors})$ (Chen–Li Lemma 4.4)
-- statement:
--   For **any** sample set $\Omega$, any $t\in\mathbb{R}$, and any factored matrices $AC^\top$ and $BD^\top$ (with $A,B,C,D$ having $d$ rows),
--
--   $$\bigl|\langle P_\Omega(AC^\top),P_\Omega(BD^\top)\rangle-t\langle AC^\top,BD^\top\rangle\bigr|\ \le\ \|\Omega-tJ\|\cdot\sqrt{\sum_k\|A_k\|^2\|B_k\|^2}\cdot\sqrt{\sum_k\|C_k\|^2\|D_k\|^2},$$
--
--   where $\|\Omega-tJ\|$ is the spectral norm of the 0/1 indicator matrix of $\Omega$ minus $t$ times the all-ones matrix, and $A_k$ denotes the $k$-th row. This is a **deterministic** inequality — no sampling model, no probability. It is the engine of the Chen–Li proof: every sampling-deviation term is controlled by the single scalar $\|\Omega-pJ\|$, replacing the union-bound-plus-net concentration machinery of Ge–Lee–Ma (their Theorem D.1) with linear algebra.
--
--   **Formalization Note** Stated for square index sets $\Omega\subseteq[d]\times[d]$ (the case used in this mission); Chen–Li state it for general rectangular index sets.
-- source:
--   Chen, Li 2019, Model-free Nonconvex Matrix Completion: Local Minima Analysis and Applications in Memory-efficient Kernel PCA, JMLR 20(142), https://arxiv.org/abs/1711.01742 (v3) [THE canonical reference: all milestones follow its Section 4], pp. 17-18, Lemma 4.4, eq. (4.3) (deterministic; stated there for general rectangular index sets, formalized here for the square symmetric case in use). Chen-Li note it replaces the concentration Theorem D.1 of Ge, Lee, Ma 2016, Matrix Completion has No Spurious Local Minimum, https://arxiv.org/abs/1605.07272 (v4); proof after Bhojanapalli-Jain 2014, Li et al. 2016.

import Definitions.Def_MCNoSpuriousMinModel
open Matrix MatrixCompletion.NoSpuriousMin

theorem MatrixCompletion.NoSpuriousMin.sampling_deviation_bound
    {d r₁ r₂ : ℕ} (Ω : Finset (Fin d × Fin d)) (t : ℝ)
    (A : Matrix (Fin d) (Fin r₁) ℝ) (B : Matrix (Fin d) (Fin r₂) ℝ)
    (C : Matrix (Fin d) (Fin r₁) ℝ) (D : Matrix (Fin d) (Fin r₂) ℝ) :
    |sampDev Ω t (A * Cᵀ) (B * Dᵀ)| ≤
      sampDevNorm Ω t
        * Real.sqrt (∑ k, vecNorm (A k) ^ 2 * vecNorm (B k) ^ 2)
        * Real.sqrt (∑ k, vecNorm (C k) ^ 2 * vecNorm (D k) ^ 2) := by sorry
