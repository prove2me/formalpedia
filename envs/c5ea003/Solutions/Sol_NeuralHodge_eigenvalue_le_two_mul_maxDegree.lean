-- Prove2me | solution 1 for NeuralHodge.eigenvalue_le_two_mul_maxDegree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:04:01.893638+00:00
-- url     : https://prove2.me/submissions/740e2a10-f9e7-4b6b-ace5-62a5a496a342

-- Sol generated from Combinatorics/NeuralhodgeBounds/NeuralHodge_Bounds.lean
import Mathlib
import Definitions.Def_Combinatorics_NeuralhodgeBounds_NeuralHodge_Bounds
import Definitions.Def_Combinatorics_NeuralhodgeDefs_NeuralHodge_Defs
import Theorems.Thm_NeuralHodge_dot_laplacian_eq_energy
import Theorems.Thm_NeuralHodge_energy_le_two_mul_degree_sum

/-!
# Neural Hodge theory: energy bounds

This module previously contained only a stray relative path pointing at a
non-existent file `Shared/NeuralHodge/Bounds.lean`.  It is reconstructed here as
the quantitative layer on top of
`Shared.NeuralhodgeDefs.NeuralHodge_Defs`.

Main results:

* `NeuralHodge.dot_laplacian_eq_energy` — the **Dirichlet identity**
  `⟨x, L x⟩ = E(x)`, the discrete integration-by-parts formula;
* `NeuralHodge.energy_nonneg` and `NeuralHodge.laplacian_posSemidef` — the
  Laplacian is positive semidefinite;
* `NeuralHodge.energy_le_two_mul_degree_sum` — the **spectral upper bound**
  `E(x) ≤ 2 ∑ᵢ deg(i) · x(i)²`, whose Rayleigh-quotient form says that every
  Laplacian eigenvalue is at most twice the maximal degree;
* `NeuralHodge.eigenvalue_le_two_mul_maxDegree` — the eigenvalue form of the bound.
-/

open NeuralHodge

variable {n : ℕ}

/-! ## Auxiliary double sums -/






/-! ## The Dirichlet identity -/


/-! ## Positivity -/



/-! ## The upper bound -/




open NeuralHodge in
theorem solution(W : Weights n) (x : Fin n → ℝ) (mu D : ℝ)
    (heig : ∀ i, laplacian W x i = mu * x i)
    (hD : ∀ i, degree W i ≤ D)
    (hx : 0 < ∑ i, x i ^ 2) :
    mu ≤ 2 * D := by
  have hdot : dot x (laplacian W x) = mu * ∑ i, x i ^ 2 := by
    unfold dot
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [heig i]; ring
  have hle : ∑ i, degree W i * x i ^ 2 ≤ D * ∑ i, x i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hD i) (sq_nonneg _)
  have hmain : mu * ∑ i, x i ^ 2 ≤ 2 * (D * ∑ i, x i ^ 2) := by
    calc mu * ∑ i, x i ^ 2 = dot x (laplacian W x) := hdot.symm
      _ = energy W x := dot_laplacian_eq_energy W x
      _ ≤ 2 * ∑ i, degree W i * x i ^ 2 := energy_le_two_mul_degree_sum W x
      _ ≤ 2 * (D * ∑ i, x i ^ 2) := by linarith
  nlinarith [hmain, hx]
