-- Prove2me | Theorems.Thm_cauchy_interlacing_sorted
-- name    : cauchy_interlacing_sorted
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-04-23T04:01:39.688176+00:00
-- url     : https://prove2.me/theorems/79926678-86bb-4bd3-91b7-d379ddcccbe2
-- statement:
--   Lemma 2.1 (Cauchy Interlacing, sorted lower-half form): for any real Hermitian matrix A and injection f : beta -> alpha, the i-th sorted eigenvalue of the principal submatrix (A.submatrix f f) is >= the (i + card alpha - card beta)-th sorted eigenvalue of A.
-- source:
--   Huang, Hao. "Induced subgraphs of hypercubes and a proof of the sensitivity conjecture." Annals of Mathematics 190.3 (2019): 949-955.

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Star

/-!
# Lemma 2.1 — Cauchy Interlacing, sorted form (lower half)

Huang 2019, Lemma 2.1: for a symmetric `n × n` matrix `A` with eigenvalues
`λ_1 ≥ λ_2 ≥ … ≥ λ_n` and an `m × m` principal submatrix `B` with eigenvalues
`μ_1 ≥ … ≥ μ_m`, we have `λ_i ≥ μ_i ≥ λ_{i+n-m}` for all `1 ≤ i ≤ m`.

This file states the *lower* half `μ_i ≥ λ_{i+n-m}` — the half actually used by
Huang's main argument (applied at `i = 0` to get `λ_max(A_H) ≥ √n`). Indices are
0-based `Fin` positions; eigenvalues are arranged in *descending* order by
`Matrix.IsHermitian.eigenvalues₀`.

This is pure spectral theory and is **not currently in Mathlib**.
-/

/-- **Lemma 2.1 — Cauchy Interlacing, sorted form (lower half).**
For any real Hermitian matrix `A : Matrix α α ℝ` and any injection `f : β ↪ α`,
the `i`-th sorted eigenvalue of the principal submatrix `A.submatrix f f` is
at least the `(i + (card α − card β))`-th sorted eigenvalue of `A`. -/

theorem cauchy_interlacing_sorted
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {A : Matrix α α ℝ} (hA : A.IsHermitian) (f : β ↪ α)
    (i : Fin (Fintype.card β)) :
    hA.eigenvalues₀
        ⟨(i : ℕ) + (Fintype.card α - Fintype.card β), by
          have hle : Fintype.card β ≤ Fintype.card α :=
            Fintype.card_le_of_injective f f.injective
          have hi : (i : ℕ) < Fintype.card β := i.isLt
          omega⟩
      ≤ (hA.submatrix (f : β → α)).eigenvalues₀ i := by sorry
