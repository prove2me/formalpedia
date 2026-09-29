-- Prove2me | solution 1 for NeuralHodge.dot_laplacian_eq_energy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:18:05.085382+00:00
-- url     : https://prove2.me/submissions/49f98328-f311-44e3-a298-548d6434f873

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


/-! ## The Dirichlet identity -/


/-! ## Positivity -/



/-! ## The upper bound -/




open NeuralHodge in
theorem solution(W : Weights n) (x : Fin n → ℝ) :
    dot x (laplacian W x) = energy W x := by
  have hdot : dot x (laplacian W x) = S1 W x - S3 W x := by
    unfold dot laplacian S1 S3
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ∑ j, W.w i j * x i ^ 2 = (∑ j, W.w i j) * x i ^ 2 := (Finset.sum_mul ..).symm
    have h2 : ∑ j, W.w i j * (x i * x j) = x i * ∑ j, W.w i j * x j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1, h2, degree]
    ring
  have key : ∑ i, ∑ j, W.w i j * (x i - x j) ^ 2 = S1 W x - 2 * S3 W x + S2 W x := by
    unfold S1 S2 S3
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hdot, energy, key, S2_eq_S1]
  ring
