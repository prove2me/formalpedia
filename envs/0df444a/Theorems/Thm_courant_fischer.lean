-- Prove2me | Theorems.Thm_courant_fischer
-- name    : courant_fischer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-03T01:04:45.658932+00:00
-- url     : https://prove2.me/theorems/d2c2983d-3726-4af6-bb84-dad579bedd20
-- statement:
--   Courant-Fischer min-max characterization (descending, witness form): for any Hermitian real matrix A and descending-sorted index k, every (n-k)-dim subspace contains a vector with Rayleigh >= lambda_k, AND there exists an (n-k)-dim subspace where Rayleigh <= lambda_k. Together these give the min-max equality lambda_k = min over (n-k)-dim W of max Rayleigh on W. Applying to -A recovers the dual max-min form, so this single statement encapsulates the full Courant-Fischer theorem.
-- source:
--   Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Star

open Matrix

/-!
# Courant–Fischer min-max characterization (descending, witness form)

For any Hermitian real matrix `A : Matrix V V ℝ` and descending-sorted index
`k`, the `k`-th eigenvalue admits a min-max characterization in terms of
Rayleigh quotients on subspaces:

   `λ_k = min over (n − k)-dim subspaces W of (max Rayleigh on W).`

We package the two halves of this min-max equality in *constructive existence
form*:

* **`≥` half**: every `(n − k)`-dim subspace `W` contains a vector `v ≠ 0`
  with `λ_k ≤ Rayleigh(v)` (so the max-Rayleigh on `W` is at least `λ_k`).
* **`≤` half**: there exists an `(n − k)`-dim subspace `W` on which
  `Rayleigh(u) ≤ λ_k` for every `u ∈ W` (the max-Rayleigh on this `W` is
  at most `λ_k`).

Together these give the min-max equality. Applying the theorem to `−A`
recovers the dual *max-min* characterization
`λ_k = max over (k+1)-dim subspaces of min Rayleigh`. So this single
statement encapsulates the full Courant–Fischer theorem for sorted real
Hermitian eigenvalues.

This is a foundational spectral-theory result underlying Cauchy interlacing,
Weyl's inequalities, and most monotonicity-style arguments on sorted
eigenvalues. **Not currently in Mathlib in this form.**
-/

/-- **Courant–Fischer min-max (descending, witness form).**
For any real Hermitian `A : Matrix V V ℝ` and any descending-sorted index
`k : Fin (card V)`:

* every subspace `W ⊆ (V → ℝ)` of dimension at least `(card V) − k` contains
  a nonzero vector `v ∈ W` with `λ_k * (v ⬝ᵥ v) ≤ A *ᵥ v ⬝ᵥ v`;
* there exists a subspace `W ⊆ (V → ℝ)` of dimension exactly `(card V) − k`
  on which `A *ᵥ u ⬝ᵥ u ≤ λ_k * (u ⬝ᵥ u)` for every `u ∈ W`.

Where `λ_k := hA.eigenvalues₀ k` is the `k`-th descending eigenvalue. -/

theorem courant_fischer
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {A : Matrix V V ℝ} (hA : A.IsHermitian) (k : Fin (Fintype.card V)) :
    (∀ W : Submodule ℝ (V → ℝ),
        Fintype.card V - (k : ℕ) ≤ Module.finrank ℝ W →
        ∃ v ∈ W, v ≠ 0 ∧ hA.eigenvalues₀ k * (v ⬝ᵥ v) ≤ A *ᵥ v ⬝ᵥ v) ∧
    (∃ W : Submodule ℝ (V → ℝ),
        Module.finrank ℝ W = Fintype.card V - (k : ℕ) ∧
        ∀ u ∈ W, A *ᵥ u ⬝ᵥ u ≤ hA.eigenvalues₀ k * (u ⬝ᵥ u)) := by sorry
