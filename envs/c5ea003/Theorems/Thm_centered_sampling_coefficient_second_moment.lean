-- Prove2me | Theorems.Thm_centered_sampling_coefficient_second_moment
-- name    : centered_sampling_coefficient_second_moment
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T21:06:18.465754+00:00
-- url     : https://prove2.me/theorems/1a4e84b8-3821-4cbd-b24c-f8b9106d0560
-- statement:
--   **Exact second moment (variance) of the scalar centered sampling coefficient.** For $\mathrm{Coeff}(\Omega)=\texttt{matrixEntrySum}(\texttt{centeredSamplingFluctuation}(\Omega,p,B))=\sum_{ij}p^{-1}(\mathbf{1}[(i,j)\in\Omega]-p)B_{ij}$ and $p\neq 0$: $$\mathbb{E}[\mathrm{Coeff}^2] = \frac{1-p}{p}\,\|B\|_F^2.$$ Proof: write $\mathrm{Coeff}=\sum_w h_w(\mathbf{1}[w\in\Omega])$ with $h_w(x)=p^{-1}B_w(x-p)$; square to a double sum; push the expectation through both sums; the diagonal $w=w'$ gives the single-coordinate second moment $p\,h_w(1)^2+(1-p)h_w(0)^2=\frac{1-p}{p}B_w^2$, while every off-diagonal $w\neq w'$ term factorizes (pair independence) into a product of two single-coordinate means, each zero (centered terms). Only the diagonal survives. This is the variance $\sigma^2$ input to the q-moment Bernstein estimate.
-- source:
--   Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013), Ch. 15; Candès–Recht 2009, arXiv:0805.4471, §6 (centered sampling operator p⁻¹(P_Ω − p)).

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators

theorem centered_sampling_coefficient_second_moment {n₁ n₂ : ℕ} (p : ℝ) (hp : p ≠ 0)
    (B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    bernoulliExpectation p
      (fun Omega => (matrixEntrySum (centeredSamplingFluctuation Omega p B)) ^ 2) =
      ((1 - p) / p) * frobeniusNormSq B := by sorry
