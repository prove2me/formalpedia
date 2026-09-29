-- Prove2me | solution 1 for Round7DigitLattice.exists_spurious_solution
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:27:12.508357+00:00
-- url     : https://prove2.me/submissions/5446935c-26c4-4331-9fda-8df06d1aa422

-- Sol generated from Tropical/Round7DigitLattice.lean
import Mathlib
import Definitions.Def_Tropical_Round7DigitLattice

/-!
# Round-7 closure DIGITLATTICE: the digit-convolution relaxation is not isolated

Experiment 328 linearised the base-`b` digit equations of `N = p q` by setting
`w_{ij} = p_i q_j` and observed that the factorisation target sits *at* the
Gaussian heuristic, so lattice reduction returns generic short vectors instead
of the factorisation.  This file proves the exact structural reason, in the
smallest nontrivial case (two digits per factor), and it is a statement about
*all* `N`, not a heuristic:

* `digitVal_rankOne` : the encoding is faithful — the digit convolution of a
  rank-one matrix `w = u ⊗ v` evaluates to the product of the two numbers
  `u₀ + u₁ b` and `v₀ + v₁ b`.  Factorisations are exactly the rank-one
  solutions.
* `det_rankOne` : rank-one matrices have vanishing determinant; the determinant
  is therefore the obstruction that the linear relaxation throws away.
* `commutator_digitVal` : the "carry commutator" `w = [[0,1],[-1,0]]` lies in the
  kernel of the digit functional for *every* base `b`.  It has squared norm `2`,
  a constant independent of `N`.
* `exists_spurious_solution` : consequently every factorisation target has a
  **non-rank-one companion solution at squared distance at most `8`** — the
  relaxed problem has spurious solutions in an `O(1)` ball around the target,
  whatever the size of `N`.  Since the target's own squared norm grows like the
  product of the digit norms (`sqNorm_rankOne_ge_four` gives the first step),
  short-vector search cannot separate the factorisation from the noise.
-/

open Round7DigitLattice

open Finset















open Round7DigitLattice in
theorem solution(b : ℤ) (u v : Fin 2 → ℤ) :
    ∃ w : Matrix (Fin 2) (Fin 2) ℤ,
      digitVal b w = digitVal b (rankOne u v) ∧ w.det ≠ 0 ∧
        sqNorm (w - rankOne u v) ≤ 8 := by
  -- perturb the target by `c • commMat` with `c ∈ {1, 2}`
  have key : ∀ c : ℤ, digitVal b (rankOne u v + c • commMat) = digitVal b (rankOne u v) := by
    intro c
    simp [digitVal, Fin.sum_univ_two, commMat, Matrix.add_apply]
    ring
  have hdet : ∀ c : ℤ, (rankOne u v + c • commMat).det
      = c * (u 0 * v 1 - u 1 * v 0) + c ^ 2 := by
    intro c
    rw [Matrix.det_fin_two]
    simp [rankOne, commMat, Matrix.add_apply]
    ring
  have hdist : ∀ c : ℤ, sqNorm ((rankOne u v + c • commMat) - rankOne u v) = 2 * c ^ 2 := by
    intro c
    have : (rankOne u v + c • commMat) - rankOne u v = c • commMat := by
      abel
    rw [this]
    simp [sqNorm, commMat, Matrix.smul_apply, Fin.sum_univ_two]
    ring
  set D : ℤ := u 0 * v 1 - u 1 * v 0 with hD
  by_cases hD1 : D + 1 = 0
  · -- use `c = 2`
    refine ⟨rankOne u v + (2 : ℤ) • commMat, key 2, ?_, ?_⟩
    · have hDv : D = -1 := by omega
      rw [hdet 2, hDv]; norm_num
    · rw [hdist 2]; norm_num
  · -- use `c = 1`
    refine ⟨rankOne u v + (1 : ℤ) • commMat, key 1, ?_, ?_⟩
    · rw [hdet 1]
      simpa using hD1
    · rw [hdist 1]; norm_num
