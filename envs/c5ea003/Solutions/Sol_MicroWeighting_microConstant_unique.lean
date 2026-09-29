-- Prove2me | solution 1 for MicroWeighting.microConstant_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:43:16.062058+00:00
-- url     : https://prove2.me/submissions/7fc1d5d4-1641-4105-bd9f-b1a22022f547

-- Sol generated from Applications/MicroscopicWeighting/Core.lean
import Mathlib
import Definitions.Def_Applications_MicroscopicWeighting_Core

/-!
# Microscopic weightings of finite metric spaces

In Leinster's magnitude theory a **weighting** of a finite metric space with
similarity matrix `Z_t` (entries `exp(-t·d(x_i,x_j))`) is a vector `w` with
`Z_t w = 𝟙`. As the scale `t → 0` one has `Z_t = J - t·D + O(t²)` with `J` the
all-ones matrix and `D` the **distance matrix**; a first-order analysis of
`Z_t w_t = 𝟙` shows the limiting ("microscopic") weighting `μ` satisfies

  `D μ = λ·𝟙`   and   `Σ μ = 1`

for a scalar `λ`. This file develops the elementary theory of such
*distance-matrix weightings*: the constant `λ` is well defined for symmetric `D`,
the weighting is unique when `D` is invertible, and it exists (via `D⁻¹`).

The heuristic of the research theme — that the microscopic weighting emphasises
boundary points, giving positive weight to vertices of the convex hull and
non-positive weight to interior points — is made concrete in `Examples.lean`.
-/

open MicroWeighting

open Matrix BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]







open MicroWeighting in
omit [DecidableEq n] in
theorem solution{D : Matrix n n ℝ} (hD : Dᵀ = D)
    {w w' : n → ℝ} {a b : ℝ}
    (hw : IsMicroWeighting D w a) (hw' : IsMicroWeighting D w' b) :
    a = b := by
  obtain ⟨hDw, hsum⟩ := hw
  obtain ⟨hDw', hsum'⟩ := hw'
  -- `w ⬝ᵥ (D w') = b·Σw = b`, and by symmetry it also `= (D w) ⬝ᵥ w' = a·Σw' = a`.
  have key : w ⬝ᵥ (D *ᵥ w') = (D *ᵥ w) ⬝ᵥ w' := by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hD]
  rw [hDw, hDw'] at key
  simp only [dotProduct] at key
  -- reduce both sides using the sums
  have lhs : ∑ i, w i * b = b := by
    rw [← Finset.sum_mul, hsum, one_mul]
  have rhs : ∑ i, a * w' i = a := by
    rw [← Finset.mul_sum, hsum', mul_one]
  -- `key : ∑ i, w i * (D w')ᵢ = ∑ i, (D w)ᵢ * w' i`; rewrite via the constants
  have hba : ∑ i, w i * b = ∑ i, a * w' i := by simpa [mul_comm] using key
  rw [lhs, rhs] at hba
  exact hba.symm
