-- Prove2me | solution 1 for lean_workbook_plus_35030
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:26:36.731755+00:00
-- url     : https://prove2.me/submissions/00d5b56e-5d9d-4495-937f-5177921f01da

import Mathlib

set_option autoImplicit false

namespace FloorDifferenceIntegerRange

noncomputable def value (x : ℝ) (k : ℤ) : ℝ :=
  x * ⌊((k : ℝ) - 1) / x⌋ - (x + 1) * ⌊(k : ℝ) / (x + 1)⌋

def integerValue (r k : ℤ) : ℤ :=
  r * ((k - 1) / r) - (r + 1) * (k / (r + 1))

theorem integer_cast (r k : ℤ) (hr : 0 < r) :
    value (r : ℝ) k = (integerValue r k : ℝ) := by
  have hcast : (r : ℝ) + 1 = ((r + 1 : ℤ) : ℝ) := by norm_cast
  have hsub : (k : ℝ) - 1 = ((k - 1 : ℤ) : ℝ) := by norm_cast
  simp only [value, hcast, hsub, Int.floor_div_cast_of_nonneg hr.le,
    Int.floor_div_cast_of_nonneg (by omega : 0 ≤ r + 1), Int.floor_intCast]
  simp [integerValue]

theorem remainder_identity (r k : ℤ) :
    integerValue r k = k % (r + 1) - (k - 1) % r - 1 := by
  have h1 := Int.emod_add_mul_ediv (k - 1) r
  have h2 := Int.emod_add_mul_ediv k (r + 1)
  unfold integerValue
  nlinarith only [h1, h2]

theorem integer_bounds (r k : ℤ) (hr : 0 < r) :
    -r ≤ integerValue r k ∧ integerValue r k ≤ r - 1 := by
  rw [remainder_identity]
  have h1 := Int.emod_nonneg k (by omega : r + 1 ≠ 0)
  have h2 := Int.emod_lt_of_pos k (by omega : 0 < r + 1)
  have h3 := Int.emod_nonneg (k - 1) (ne_of_gt hr)
  have h4 := Int.emod_lt_of_pos (k - 1) hr
  omega

theorem periodic (r k : ℤ) :
    integerValue r (k + r * (r + 1)) = integerValue r k := by
  rw [remainder_identity, remainder_identity]
  have he : k + r * (r + 1) - 1 = (k - 1) + r * (r + 1) := by ring
  rw [he]
  simp [Int.add_emod]

theorem negative_value (r j : ℤ) (_hr : 0 < r) (hj : 1 ≤ j) (hjr : j ≤ r) :
    integerValue r ((r + 1) * j) = -j := by
  rw [remainder_identity]
  have he : (r + 1) * j - 1 = r * j + (j - 1) := by ring
  rw [he]
  have hjmod : (j - 1) % r = j - 1 := Int.emod_eq_of_lt (by omega) (by omega)
  simp [Int.add_emod, hjmod]

theorem nonnegative_value (r j : ℤ) (_hr : 0 < r) (hj : 0 ≤ j) (hjr : j < r) :
    integerValue r (1 + r * (r + 1 - j)) = j := by
  rw [remainder_identity]
  have hsub : 1 + r * (r + 1 - j) - 1 = r * (r + 1 - j) := by ring
  have he : 1 + r * (r + 1 - j) = (r + 1) * (r - j) + (j + 1) := by ring
  rw [hsub, he]
  have hjmod : (j + 1) % (r + 1) = j + 1 := Int.emod_eq_of_lt (by omega) (by omega)
  simp [Int.add_emod, hjmod]

theorem exact_integer_range (r : ℤ) (hr : 0 < r) :
    {v : ℤ | ∃ k : ℤ, 0 < k ∧ integerValue r k = v} = Set.Icc (-r) (r - 1) := by
  ext v
  constructor
  · rintro ⟨k, _, rfl⟩
    exact integer_bounds r k hr
  · intro hv
    rcases hv with ⟨hlo, hhi⟩
    by_cases hv0 : 0 ≤ v
    · refine ⟨1 + r * (r + 1 - v), ?_, nonnegative_value r v hr hv0 (by omega)⟩
      have h : 0 < r + 1 - v := by omega
      positivity
    · refine ⟨(r + 1) * (-v), ?_, ?_⟩
      · have h : 0 < -v := by omega
        positivity
      · simpa using negative_value r (-v) hr (by omega) (by omega)

theorem attains_integer (r v : ℤ) (hr : 0 < r) (hv : -r ≤ v ∧ v ≤ r - 1) :
    ∃ k : ℤ, 0 < k ∧ value (r : ℝ) k = (v : ℝ) := by
  have hmem : v ∈ {w : ℤ | ∃ k : ℤ, 0 < k ∧ integerValue r k = w} := by
    rw [exact_integer_range r hr]
    exact hv
  obtain ⟨k, hk, he⟩ := hmem
  exact ⟨k, hk, by rw [integer_cast r k hr, he]⟩

theorem real_integer_bounds (r k : ℤ) (hr : 0 < r) :
    -(r : ℝ) ≤ value (r : ℝ) k ∧ value (r : ℝ) k ≤ (r : ℝ) - 1 := by
  rw [integer_cast r k hr]
  exact_mod_cast integer_bounds r k hr

theorem real_periodic (r k : ℤ) (hr : 0 < r) :
    value (r : ℝ) (k + r * (r + 1)) = value (r : ℝ) k := by
  rw [integer_cast r _ hr, integer_cast r _ hr, periodic]

theorem exact_real_integer_range (r : ℤ) (hr : 0 < r) :
    {v : ℝ | ∃ k : ℤ, 0 < k ∧ value (r : ℝ) k = v} =
      (Int.cast : ℤ → ℝ) '' Set.Icc (-r) (r - 1) := by
  ext v
  constructor
  · rintro ⟨k, _, rfl⟩
    exact ⟨integerValue r k, integer_bounds r k hr, (integer_cast r k hr).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact attains_integer r v hr hv

theorem integer_source_iff (r : ℤ) (hr : 0 < r) :
    (∀ k : ℤ, 0 < k → value (r : ℝ) k ≤ 0) ↔ r = 1 := by
  constructor
  · intro h
    obtain ⟨k, hk, he⟩ := attains_integer r (r - 1) hr ⟨by omega, le_rfl⟩
    have hz := h k hk
    rw [he] at hz
    have hi : r - 1 ≤ 0 := by exact_mod_cast hz
    omega
  · rintro rfl k _
    simpa using (real_integer_bounds 1 k (by norm_num)).2

theorem integer_maximum (r : ℤ) (hr : 0 < r) :
    IsGreatest {v : ℤ | ∃ k : ℤ, 0 < k ∧ integerValue r k = v} (r - 1) := by
  rw [exact_integer_range r hr]
  exact ⟨⟨by omega, le_rfl⟩, fun _ h => h.2⟩

theorem integer_minimum (r : ℤ) (hr : 0 < r) :
    IsLeast {v : ℤ | ∃ k : ℤ, 0 < k ∧ integerValue r k = v} (-r) := by
  rw [exact_integer_range r hr]
  exact ⟨⟨le_rfl, by omega⟩, fun _ h => h.1⟩

theorem real_bounds (x : ℝ) (k : ℤ) (hx : 0 < x) :
    -x - 1 < value x k ∧ value x k < x := by
  have hx1 : 0 < x + 1 := by linarith
  have h1 := Int.sub_floor_div_mul_nonneg ((k : ℝ) - 1) hx
  have h2 := Int.sub_floor_div_mul_lt ((k : ℝ) - 1) hx
  have h3 := Int.sub_floor_div_mul_nonneg (k : ℝ) hx1
  have h4 := Int.sub_floor_div_mul_lt (k : ℝ) hx1
  unfold value
  constructor <;> nlinarith only [h1, h2, h3, h4]

theorem source_counterexample : value 2 5 = 1 := by
  norm_num [value]
  rfl

theorem source_false :
    ¬ (∀ x : ℝ, 0 < x → ∀ k : ℤ, 0 < k → value x k ≤ 0) := by
  intro h
  have hc := h 2 (by norm_num) 5 (by norm_num)
  rw [source_counterexample] at hc
  norm_num at hc

theorem positive_counterexamples (r : ℤ) (hr : 2 ≤ r) :
    ∃ k : ℤ, 0 < k ∧ 0 < value (r : ℝ) k := by
  obtain ⟨k, hk, he⟩ := attains_integer r (r - 1) (by omega) ⟨by omega, le_rfl⟩
  refine ⟨k, hk, ?_⟩
  rw [he]
  exact_mod_cast (show 0 < r - 1 by omega)

theorem unbounded_above (N : ℕ) :
    ∃ x : ℝ, 0 < x ∧ ∃ k : ℤ, 0 < k ∧ (N : ℝ) < value x k := by
  obtain ⟨k, hk, he⟩ := attains_integer (N + 2) (N + 1) (by omega) ⟨by omega, by omega⟩
  refine ⟨((N + 2 : ℤ) : ℝ), by positivity, k, hk, ?_⟩
  rw [he]
  norm_cast
  omega

theorem unbounded_below (N : ℕ) :
    ∃ x : ℝ, 0 < x ∧ ∃ k : ℤ, 0 < k ∧ value x k < -(N : ℝ) := by
  obtain ⟨k, hk, he⟩ := attains_integer (N + 1) (-(N + 1)) (by omega) ⟨by omega, by omega⟩
  refine ⟨((N + 1 : ℤ) : ℝ), by positivity, k, hk, ?_⟩
  rw [he]
  norm_cast
  omega

theorem posted_identity (x : ℝ) (k : ℤ) (hx : 0 < x) :
    x * (k - 1) / x - (x + 1) * k / (x + 1) = -1 := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx1 : x + 1 ≠ 0 := by positivity
  field_simp
  ring

end FloorDifferenceIntegerRange

theorem solution (x : ℝ) (k : ℤ) (hx : 0 < x) (_hk : 0 < k) :
    x * (k - 1) / x - (x + 1) * k / (x + 1) ≤ 0 := by
  rw [FloorDifferenceIntegerRange.posted_identity x k hx]
  norm_num

#print axioms FloorDifferenceIntegerRange.value
#print axioms FloorDifferenceIntegerRange.integerValue
#print axioms FloorDifferenceIntegerRange.integer_cast
#print axioms FloorDifferenceIntegerRange.remainder_identity
#print axioms FloorDifferenceIntegerRange.integer_bounds
#print axioms FloorDifferenceIntegerRange.periodic
#print axioms FloorDifferenceIntegerRange.negative_value
#print axioms FloorDifferenceIntegerRange.nonnegative_value
#print axioms FloorDifferenceIntegerRange.exact_integer_range
#print axioms FloorDifferenceIntegerRange.attains_integer
#print axioms FloorDifferenceIntegerRange.real_integer_bounds
#print axioms FloorDifferenceIntegerRange.real_periodic
#print axioms FloorDifferenceIntegerRange.exact_real_integer_range
#print axioms FloorDifferenceIntegerRange.integer_source_iff
#print axioms FloorDifferenceIntegerRange.integer_maximum
#print axioms FloorDifferenceIntegerRange.integer_minimum
#print axioms FloorDifferenceIntegerRange.real_bounds
#print axioms FloorDifferenceIntegerRange.source_counterexample
#print axioms FloorDifferenceIntegerRange.source_false
#print axioms FloorDifferenceIntegerRange.positive_counterexamples
#print axioms FloorDifferenceIntegerRange.unbounded_above
#print axioms FloorDifferenceIntegerRange.unbounded_below
#print axioms FloorDifferenceIntegerRange.posted_identity
#print axioms solution
