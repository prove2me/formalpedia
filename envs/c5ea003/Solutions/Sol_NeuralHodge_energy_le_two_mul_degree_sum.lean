-- Prove2me | solution 1 for NeuralHodge.energy_le_two_mul_degree_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:18:05.802216+00:00
-- url     : https://prove2.me/submissions/090c0182-a7ff-47e1-9912-e1953d6454cd

-- Sol generated from Combinatorics/NeuralhodgeBounds/NeuralHodge_Bounds.lean
import Mathlib
import Definitions.Def_Combinatorics_NeuralhodgeBounds_NeuralHodge_Bounds
import Definitions.Def_Combinatorics_NeuralhodgeDefs_NeuralHodge_Defs

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

private noncomputable def S1 (W : Weights n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, W.w i j * x i ^ 2

private noncomputable def S2 (W : Weights n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, W.w i j * x j ^ 2

private noncomputable def S3 (W : Weights n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, W.w i j * (x i * x j)


/-! ## Auxiliary double sums -/




/-- Symmetry of the weights identifies the two "square" double sums. -/
private lemma S2_eq_S1 (W : Weights n) (x : Fin n → ℝ) : S2 W x = S1 W x := by
  unfold S1 S2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [W.w_symm j i]

/-- `S₁` is the degree-weighted square sum. -/
private lemma S1_eq_degree_sum (W : Weights n) (x : Fin n → ℝ) :
    S1 W x = ∑ i, degree W i * x i ^ 2 := by
  unfold S1 degree
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]

/-! ## The Dirichlet identity -/


/-! ## Positivity -/



/-! ## The upper bound -/




open NeuralHodge in
theorem solution(W : Weights n) (x : Fin n → ℝ) :
    energy W x ≤ 2 * ∑ i, degree W i * x i ^ 2 := by
  have hpt : ∀ i : Fin n, ∀ j : Fin n,
      W.w i j * (x i - x j) ^ 2 ≤ W.w i j * (2 * x i ^ 2 + 2 * x j ^ 2) := by
    intro i j
    refine mul_le_mul_of_nonneg_left ?_ (W.w_nonneg i j)
    nlinarith [sq_nonneg (x i + x j)]
  have hsum : ∑ i, ∑ j, W.w i j * (x i - x j) ^ 2
      ≤ ∑ i, ∑ j, W.w i j * (2 * x i ^ 2 + 2 * x j ^ 2) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
  have hexp : ∑ i, ∑ j, W.w i j * (2 * x i ^ 2 + 2 * x j ^ 2)
      = 2 * S1 W x + 2 * S2 W x := by
    unfold S1 S2
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hexp, S2_eq_S1, S1_eq_degree_sum] at hsum
  unfold energy
  linarith
