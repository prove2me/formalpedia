-- Prove2me | solution 1 for Catalog.MachineLearning.NoiseFloor.resolvent_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:44:07.795512+00:00
-- url     : https://prove2.me/submissions/00a45f16-5806-4380-aa91-ae8943dbfa2b

-- Sol generated from MachineLearning/NoiseFloor/TraceLemma.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Definitions.Def_MachineLearning_NoiseFloor_NoiseFloorPrinciple
/-
# The Noise-Floor Principle, Part III: the trace-lemma frontier

Round-6 hypothesis closure, Phase A.

Parts I and II worked with an abstract spectrum `a : ι → ℝ`.  This file closes
the loop with genuine matrices: for a real positive semidefinite covariance
`A` and noise level `b > 0` we build the resolvent `(A + b•1)⁻¹` explicitly out
of the spectral decomposition and prove the **trace lemma**

  `tr (A (A + b•1)⁻¹) = ∑ i, μ i / (μ i + b) = effDim μ b`,

where `μ` are the eigenvalues of `A`.  Consequently the exact minimum of the
spectral learning risk of Part II is the *analytic* quantity
`b · tr (A (A + b•1)⁻¹)` — the noise floor is a trace functional of the data
covariance alone.  We then push the frontier: the trace functional is squeezed
between `0` and `min (tr A / b) (rank A) (n)`.

## Main results

* `resolvent_eq`              — explicit diagonalisation of `(A + b•1)⁻¹`
* `trace_resolvent_eq_effDim` — the trace lemma
* `noiseFloor_eq_b_mul_trace` — the noise floor is `b · tr (A (A+b•1)⁻¹)`
* `isLeast_filterRisk_matrix` — variational form: the minimum risk of *every*
  spectral filter equals `b · tr (A (A+b•1)⁻¹)`
* `trace_resolvent_le_trace_div`, `trace_resolvent_le_card`,
  `trace_resolvent_le_rank` — the three frontier bounds
* `noiseFloor_matrix_le_min`  — `b·tr(A(A+b)⁻¹) ≤ min (tr A) (n b)`
-/

open Catalog.MachineLearning.NoiseFloor

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]


variable {A : Matrix n n ℝ} {b : ℝ}

/-- Spectral decomposition in the concrete `U D Uᵀ` form. -/
lemma spectral_conj (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℝ) * diagonal hA.eigenvalues *
      star (hA.eigenvectorUnitary : Matrix n n ℝ) := by
  have h := hA.spectral_theorem
  simpa [Unitary.conjStarAlgAut, Function.comp] using h

/-- Conjugation by the eigenvector unitary is multiplicative. -/
lemma conj_mul_conj (hA : A.IsHermitian) (D₁ D₂ : Matrix n n ℝ) :
    ((hA.eigenvectorUnitary : Matrix n n ℝ) * D₁ * star (hA.eigenvectorUnitary : Matrix n n ℝ)) *
      ((hA.eigenvectorUnitary : Matrix n n ℝ) * D₂ *
        star (hA.eigenvectorUnitary : Matrix n n ℝ))
      = (hA.eigenvectorUnitary : Matrix n n ℝ) * (D₁ * D₂) *
        star (hA.eigenvectorUnitary : Matrix n n ℝ) := by
  have h1 : star (hA.eigenvectorUnitary : Matrix n n ℝ) *
      (hA.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star (hA.eigenvectorUnitary : Matrix n n ℝ)), h1, Matrix.one_mul]






variable {A : Matrix n n ℝ} {b : ℝ}










/-- A worked instance: the `2 × 2` covariance `diag(1, 0)` at noise level `1`.
Its resolvent trace is `1/2`, so the noise floor is `1/2` — one half of one
resolvable mode, even though the ambient dimension is `2` and the rank is `1`.
This is the matrix incarnation of the two-mode separation of Part II. -/
example : effDim (![1, 0] : Fin 2 → ℝ) 1 = 1 / 2 := by
  rw [effDim]
  simp [Fin.sum_univ_two]
  norm_num



open Catalog.MachineLearning.NoiseFloor in
theorem solution(hA : A.IsHermitian) (hpsd : A.PosSemidef) (hb : 0 < b) :
    (A + b • (1 : Matrix n n ℝ))⁻¹ =
      (hA.eigenvectorUnitary : Matrix n n ℝ) * diagonal (fun i => (hA.eigenvalues i + b)⁻¹) *
        star (hA.eigenvectorUnitary : Matrix n n ℝ) := by
  have h2 : (hA.eigenvectorUnitary : Matrix n n ℝ) *
      star (hA.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hne : ∀ i, hA.eigenvalues i + b ≠ 0 := by
    intro i
    have h0 : (0:ℝ) ≤ hA.eigenvalues i := hpsd.eigenvalues_nonneg i
    positivity
  have hd : diagonal (fun i => hA.eigenvalues i + b)
      = diagonal hA.eigenvalues + b • (1 : Matrix n n ℝ) := by
    rw [Matrix.smul_one_eq_diagonal, ← diagonal_add]
  have hsum : (hA.eigenvectorUnitary : Matrix n n ℝ) * diagonal (fun i => hA.eigenvalues i + b) *
      star (hA.eigenvectorUnitary : Matrix n n ℝ) = A + b • (1 : Matrix n n ℝ) := by
    rw [hd, Matrix.mul_add, Matrix.add_mul, ← spectral_conj hA, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, h2]
  apply Matrix.inv_eq_right_inv
  rw [← hsum, conj_mul_conj hA, diagonal_mul_diagonal]
  rw [show (fun i => (hA.eigenvalues i + b) * (hA.eigenvalues i + b)⁻¹) = fun _ => (1 : ℝ) from
    funext fun i => mul_inv_cancel₀ (hne i)]
  rw [diagonal_one, Matrix.mul_one, h2]
