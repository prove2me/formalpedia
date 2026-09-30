-- Prove2me | solution 1 for lean_workbook_plus_13113
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:28:53.378709+00:00
-- url     : https://prove2.me/submissions/15cff0e0-1acc-4281-8987-34e3dda55b3f

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace InverseCubicProductMinimum

def value (r x : ℝ) : ℝ := (1 + x) ^ 3 * (1 + r ^ 4 / x ^ 3)

def remainder (r x : ℝ) : ℝ :=
  x ^ 4 + (3 + 2 * r) * x ^ 3 + 3 * (1 + r) ^ 2 * x ^ 2 + r * (2 + 3 * r) * x + r ^ 2

def attainable (r : ℝ) : Set ℝ := {v | ∃ x : ℝ, 0 < x ∧ value r x = v}

theorem polynomial_certificate (r x : ℝ) :
    (1 + x) ^ 3 * (x ^ 3 + r ^ 4) - (1 + r) ^ 4 * x ^ 3 =
      (x - r) ^ 2 * remainder r x := by
  dsimp [remainder]
  ring

theorem positive_remainder (r x : ℝ) (hr : 0 ≤ r) (hx : 0 < x) :
    0 < remainder r x := by
  dsimp [remainder]
  positivity

theorem gap_identity (r x : ℝ) (hx : 0 < x) :
    value r x - (1 + r) ^ 4 = (x - r) ^ 2 * remainder r x / x ^ 3 := by
  dsimp [value]
  apply (eq_div_iff (ne_of_gt (by positivity : 0 < x ^ 3))).mpr
  have h := polynomial_certificate r x
  field_simp
  nlinarith only [h]

theorem bound (r x : ℝ) (hr : 0 ≤ r) (hx : 0 < x) : (1 + r) ^ 4 ≤ value r x := by
  have h := gap_identity r x hx
  have hp : 0 ≤ (x - r) ^ 2 * remainder r x / x ^ 3 := by
    have := positive_remainder r x hr hx
    positivity
  linarith only [h, hp]

theorem equality_iff (r x : ℝ) (hr : 0 ≤ r) (hx : 0 < x) :
    value r x = (1 + r) ^ 4 ↔ x = r := by
  constructor
  · intro he
    have h := gap_identity r x hx
    rw [he, sub_self] at h
    have hnum : (x - r) ^ 2 * remainder r x = 0 :=
      (div_eq_zero_iff.mp h.symm).resolve_right (ne_of_gt (by positivity))
    have hz : (x - r) ^ 2 = 0 :=
      (mul_eq_zero.mp hnum).resolve_right (ne_of_gt (positive_remainder r x hr hx))
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)
  · intro he
    have h := gap_identity r x hx
    rw [he, sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_mul, zero_div] at h
    simpa only [he] using sub_eq_zero.mp h

theorem diagonal_minimum (r : ℝ) (hr : 0 < r) : value r r = (1 + r) ^ 4 :=
  (equality_iff r r hr.le hr).mpr rfl

theorem least_value (r : ℝ) (hr : 0 < r) : IsLeast (attainable r) ((1 + r) ^ 4) := by
  constructor
  · exact ⟨r, hr, diagonal_minimum r hr⟩
  · rintro v ⟨x, hx, rfl⟩
    exact bound r x hr.le hx

theorem uniform_lower_bound_iff (r k : ℝ) (hr : 0 < r) :
    (∀ x : ℝ, 0 < x → k ≤ value r x) ↔ k ≤ (1 + r) ^ 4 := by
  constructor
  · intro h
    simpa only [diagonal_minimum r hr] using h r hr
  · intro hk x hx
    exact hk.trans (bound r x hr.le hx)

theorem zero_parameter_strict (x : ℝ) (hx : 0 < x) : 1 < value 0 x := by
  have hb := bound 0 x (by norm_num) hx
  have he : value 0 x ≠ (1 + (0 : ℝ)) ^ 4 := by
    intro h
    exact hx.ne' ((equality_iff 0 x (by norm_num) hx).mp h)
  simpa only [add_zero, one_pow] using lt_of_le_of_ne hb he.symm

theorem source_equality (x : ℝ) (hx : 0 < x) :
    (1 + x) ^ 3 * (1 + 16 / x ^ 3) = 81 ↔ x = 2 := by
  have h := equality_iff 2 x (by norm_num) hx
  norm_num [value] at h
  exact h

end InverseCubicProductMinimum

theorem solution (x : ℝ) (hx : 0 < x) : (1 + x) ^ 3 * (1 + 16 / x ^ 3) ≥ 81 := by
  have h := InverseCubicProductMinimum.bound 2 x (by norm_num) hx
  norm_num [InverseCubicProductMinimum.value] at h
  exact h

#print axioms InverseCubicProductMinimum.polynomial_certificate
#print axioms InverseCubicProductMinimum.positive_remainder
#print axioms InverseCubicProductMinimum.gap_identity
#print axioms InverseCubicProductMinimum.bound
#print axioms InverseCubicProductMinimum.equality_iff
#print axioms InverseCubicProductMinimum.diagonal_minimum
#print axioms InverseCubicProductMinimum.least_value
#print axioms InverseCubicProductMinimum.uniform_lower_bound_iff
#print axioms InverseCubicProductMinimum.zero_parameter_strict
#print axioms InverseCubicProductMinimum.source_equality
#print axioms solution
