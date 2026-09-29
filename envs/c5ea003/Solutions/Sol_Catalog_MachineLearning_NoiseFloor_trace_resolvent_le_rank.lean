-- Prove2me | solution 1 for Catalog.MachineLearning.NoiseFloor.trace_resolvent_le_rank
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:45:59.05203+00:00
-- url     : https://prove2.me/submissions/2f0a74ae-a545-4090-a9bc-5802e0e5a996

-- Sol generated from MachineLearning/NoiseFloor/TraceLemma.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Definitions.Def_MachineLearning_NoiseFloor_NoiseFloorPrinciple
import Theorems.Thm_Catalog_MachineLearning_NoiseFloor_mode_mem_Ico
import Theorems.Thm_Catalog_MachineLearning_NoiseFloor_resolvent_eq
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

/-- Conjugation by a unitary preserves the trace. -/
lemma trace_conj (hA : A.IsHermitian) (D : Matrix n n ℝ) :
    ((hA.eigenvectorUnitary : Matrix n n ℝ) * D *
      star (hA.eigenvectorUnitary : Matrix n n ℝ)).trace = D.trace := by
  have h1 : star (hA.eigenvectorUnitary : Matrix n n ℝ) *
      (hA.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]


/-- **The trace lemma.**  `tr (A (A + b•1)⁻¹)` is exactly the spectral effective
dimension of `A` at level `b`.  This is the bridge between the analytic
(resolvent) and the combinatorial (mode-counting) descriptions of the noise
floor. -/
theorem trace_resolvent_eq_effDim (hA : A.IsHermitian) (hpsd : A.PosSemidef) (hb : 0 < b) :
    (A * (A + b • (1 : Matrix n n ℝ))⁻¹).trace = effDim hA.eigenvalues b := by
  rw [resolvent_eq hA hpsd hb]
  nth_rewrite 1 [spectral_conj hA]
  rw [conj_mul_conj hA, trace_conj hA, diagonal_mul_diagonal, Matrix.trace_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_eq_mul_inv]



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
    (A * (A + b • (1 : Matrix n n ℝ))⁻¹).trace ≤ (A.rank : ℝ) := by
  classical
  rw [trace_resolvent_eq_effDim hA hpsd hb, effDim]
  have hzero : ∀ i ∈ univ.filter fun i => hA.eigenvalues i = 0,
      hA.eigenvalues i / (hA.eigenvalues i + b) = 0 := by
    intro i hi
    rw [(mem_filter.1 hi).2, zero_div]
  have hsplit : ∑ i, hA.eigenvalues i / (hA.eigenvalues i + b)
      = ∑ i ∈ univ.filter fun i => hA.eigenvalues i ≠ 0,
          hA.eigenvalues i / (hA.eigenvalues i + b) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun i => hA.eigenvalues i ≠ 0)]
    have : ∑ i ∈ univ.filter fun i => ¬ (hA.eigenvalues i ≠ 0),
        hA.eigenvalues i / (hA.eigenvalues i + b) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have : hA.eigenvalues i = 0 := not_not.1 (mem_filter.1 hi).2
      rw [this, zero_div]
    rw [this, add_zero]
  rw [hsplit]
  have hbound : ∑ i ∈ univ.filter fun i => hA.eigenvalues i ≠ 0,
      hA.eigenvalues i / (hA.eigenvalues i + b)
      ≤ ((univ.filter fun i => hA.eigenvalues i ≠ 0).card : ℝ) := by
    have := Finset.sum_le_card_nsmul (univ.filter fun i => hA.eigenvalues i ≠ 0)
      (fun i => hA.eigenvalues i / (hA.eigenvalues i + b)) 1
      (fun i _ => (mode_mem_Ico (fun j => hpsd.eigenvalues_nonneg j) hb i).2.le)
    simpa using this
  have hrank : (A.rank : ℝ) = ((univ.filter fun i => hA.eigenvalues i ≠ 0).card : ℝ) := by
    rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  rw [hrank]
  exact hbound
