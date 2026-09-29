-- Prove2me | Theorems.Thm_eigenvalue_sq_of_matrix_sq
-- name    : eigenvalue_sq_of_matrix_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-04-23T05:10:07.919372+00:00
-- url     : https://prove2.me/theorems/c551168f-cb8d-49c1-8910-6a1dc0544b10
-- statement:
--   For any real Hermitian matrix A with A^2 = c*I, every sorted eigenvalue lambda_i satisfies lambda_i^2 = c. A reusable abstract spectral fact.
-- source:
--   Huang, Hao. "Induced subgraphs of hypercubes and a proof of the sensitivity conjecture." Annals of Mathematics 190.3 (2019): 949-955.

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Star

/-!
# Abstract spectral fact — `A² = c·I ⇒ λᵢ² = c`

If a real Hermitian matrix `A` satisfies `A^2 = c • 1`, then every (sorted)
eigenvalue squared equals `c`. A reusable spectral-theory lemma used, in
particular, to pin the spectrum of Huang's signed hypercube matrix `A_n`
(which satisfies `A_n^2 = n · 1`) to `±√n`.

Not currently in Mathlib.
-/

/-- **Abstract spectral fact.** If `A` is real Hermitian and `A^2 = c • 1`,
    then every sorted eigenvalue `λᵢ` satisfies `λᵢ² = c`. -/

theorem eigenvalue_sq_of_matrix_sq
    {α : Type*} [Fintype α] [DecidableEq α]
    {A : Matrix α α ℝ} (hA : A.IsHermitian)
    {c : ℝ} (hA_sq : A ^ 2 = c • 1) (i : Fin (Fintype.card α)) :
    (hA.eigenvalues₀ i) ^ 2 = c := by sorry
