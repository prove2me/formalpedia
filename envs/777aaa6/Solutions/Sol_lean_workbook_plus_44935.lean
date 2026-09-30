-- Prove2me | solution 1 for lean_workbook_plus_44935
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:05:49.764168+00:00
-- url     : https://prove2.me/submissions/2882baba-bb90-459b-ae9d-36a984fe3d0a

import Mathlib

namespace MixedQuadraticSimplexRange

def Constraint (a b c : ℝ) : Prop :=
  0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b ^ 2 + c = 1

def value (a b c : ℝ) : ℝ := (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2)

def reduced (s p : ℝ) : ℝ := (2 - s) * (1 + s ^ 2 - 2 * p + p ^ 2)

def gapFactor (s : ℝ) : ℝ := s ^ 4 - s ^ 3 + 7 * s ^ 2 - 9 * s + 7

theorem reduction {a b c : ℝ} (h : a + b ^ 2 + c = 1) :
    value a b c = reduced (a + c) (a * c) := by
  have hb : b ^ 2 = 1 - a - c := by linarith
  unfold value reduced
  rw [hb]
  ring

theorem parameters {a b c : ℝ} (h : Constraint a b c) :
    a + c ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ a * c ∧ 0 ≤ (a + c) ^ 2 - 4 * (a * c) := by
  exact ⟨⟨add_nonneg h.1 h.2.2.1, by nlinarith [h.2.2.2, sq_nonneg b]⟩,
    mul_nonneg h.1 h.2.2.1, by nlinarith [sq_nonneg (a - c)]⟩

theorem gap_factor_pos (s : ℝ) : 0 < gapFactor s := by
  have he : gapFactor s = s ^ 2 * (s - 1 / 2) ^ 2 +
      (27 / 4) * (s - 2 / 3) ^ 2 + 4 := by
    unfold gapFactor
    ring
  nlinarith only [he, mul_nonneg (sq_nonneg s) (sq_nonneg (s - 1 / 2)),
    sq_nonneg (s - 2 / 3)]

theorem coefficient_bounds {s p : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hd : 0 ≤ s ^ 2 - 4 * p) :
    0 < 2 - s ∧ 0 < 8 - 4 * p - s ^ 2 ∧ 0 < 2 - p := by
  have hs2 : s ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hs.2)]
  exact ⟨by linarith [hs.2], by linarith, by linarith⟩

theorem lower_gap (s p : ℝ) :
    16 * reduced s p - 25 = (1 - s) * gapFactor s +
      (2 - s) * (s ^ 2 - 4 * p) * (8 - 4 * p - s ^ 2) := by
  unfold reduced gapFactor
  ring

theorem upper_gap (s p : ℝ) :
    2 - reduced s p = s * (1 - s) ^ 2 + (2 - s) * p * (2 - p) := by
  unfold reduced
  ring

theorem reduced_bounds {s p : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hp : 0 ≤ p) (hd : 0 ≤ s ^ 2 - 4 * p) :
    (25 / 16 : ℝ) ≤ reduced s p ∧ reduced s p ≤ 2 := by
  obtain ⟨hc1, hc2, hc3⟩ := coefficient_bounds hs hd
  constructor
  · have h1 := mul_nonneg (sub_nonneg.mpr hs.2) (gap_factor_pos s).le
    have h2 := mul_nonneg (mul_nonneg hc1.le hd) hc2.le
    nlinarith only [lower_gap s p, h1, h2]
  · have h1 := mul_nonneg hs.1 (sq_nonneg (1 - s))
    have h2 := mul_nonneg (mul_nonneg hc1.le hp) hc3.le
    nlinarith only [upper_gap s p, h1, h2]

theorem reduced_lower_equality {s p : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hd : 0 ≤ s ^ 2 - 4 * p) :
    reduced s p = 25 / 16 ↔ s = 1 ∧ p = 1 / 4 := by
  constructor
  · intro he
    obtain ⟨hc1, hc2, _⟩ := coefficient_bounds hs hd
    have h1 := mul_nonneg (sub_nonneg.mpr hs.2) (gap_factor_pos s).le
    have h2 := mul_nonneg (mul_nonneg hc1.le hd) hc2.le
    have hz1 : (1 - s) * gapFactor s = 0 := by
      nlinarith only [lower_gap s p, he, h1, h2]
    have hz2 : (2 - s) * (s ^ 2 - 4 * p) * (8 - 4 * p - s ^ 2) = 0 := by
      nlinarith only [lower_gap s p, he, h1, h2]
    have hs1 : s = 1 := by
      have := (mul_eq_zero.mp hz1).resolve_right (gap_factor_pos s).ne'
      linarith
    have hd0 := (mul_eq_zero.mp ((mul_eq_zero.mp hz2).resolve_right hc2.ne')).resolve_left hc1.ne'
    exact ⟨hs1, by rw [hs1] at hd0; linarith⟩
  · rintro ⟨rfl, rfl⟩
    unfold reduced
    norm_num

theorem reduced_upper_equality {s p : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hp : 0 ≤ p) (hd : 0 ≤ s ^ 2 - 4 * p) :
    reduced s p = 2 ↔ (s = 0 ∧ p = 0) ∨ (s = 1 ∧ p = 0) := by
  constructor
  · intro he
    obtain ⟨hc1, _, hc3⟩ := coefficient_bounds hs hd
    have h1 := mul_nonneg hs.1 (sq_nonneg (1 - s))
    have h2 := mul_nonneg (mul_nonneg hc1.le hp) hc3.le
    have hz1 : s * (1 - s) ^ 2 = 0 := by
      nlinarith only [upper_gap s p, he, h1, h2]
    have hz2 : (2 - s) * p * (2 - p) = 0 := by
      nlinarith only [upper_gap s p, he, h1, h2]
    have hp0 := (mul_eq_zero.mp ((mul_eq_zero.mp hz2).resolve_right hc3.ne')).resolve_left hc1.ne'
    rcases mul_eq_zero.mp hz1 with hs0 | hs1
    · exact Or.inl ⟨hs0, hp0⟩
    · exact Or.inr ⟨by nlinarith only [hs1], hp0⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> unfold reduced <;> norm_num

theorem bounds {a b c : ℝ} (h : Constraint a b c) :
    (25 / 16 : ℝ) ≤ value a b c ∧ value a b c ≤ 2 := by
  rw [reduction h.2.2.2]
  obtain ⟨hs, hp, hd⟩ := parameters h
  exact reduced_bounds hs hp hd

theorem lower_equality {a b c : ℝ} (h : Constraint a b c) :
    value a b c = 25 / 16 ↔ a = 1 / 2 ∧ b = 0 ∧ c = 1 / 2 := by
  constructor
  · intro he
    rw [reduction h.2.2.2] at he
    obtain ⟨hs, _, hd⟩ := parameters h
    obtain ⟨hs1, hp⟩ := (reduced_lower_equality hs hd).mp he
    have hac : a = c := by nlinarith only [hs1, hp, sq_nonneg (a - c)]
    have ha : a = 1 / 2 := by linarith
    have hc : c = 1 / 2 := by linarith
    exact ⟨ha, by nlinarith only [h.2.2.2, hs1], hc⟩
  · rintro ⟨rfl, rfl, rfl⟩
    unfold value
    norm_num

theorem upper_equality {a b c : ℝ} (h : Constraint a b c) :
    value a b c = 2 ↔
      (a = 1 ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ b = 1 ∧ c = 0) ∨
      (a = 0 ∧ b = 0 ∧ c = 1) := by
  constructor
  · intro he
    rw [reduction h.2.2.2] at he
    obtain ⟨hs, hp, hd⟩ := parameters h
    rcases (reduced_upper_equality hs hp hd).mp he with ⟨hs0, _⟩ | ⟨hs1, hp0⟩
    · have ha : a = 0 := by linarith [h.1, h.2.2.1]
      have hc : c = 0 := by linarith [h.1, h.2.2.1]
      have hb : b = 1 := by nlinarith only [h.2.2.2, h.2.1, ha, hc]
      exact Or.inr (Or.inl ⟨ha, hb, hc⟩)
    · have hb : b = 0 := by nlinarith only [h.2.2.2, hs1]
      rcases mul_eq_zero.mp hp0 with ha | hc
      · exact Or.inr (Or.inr ⟨ha, hb, by linarith⟩)
      · exact Or.inl ⟨by linarith, hb, hc⟩
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;>
      unfold value <;> norm_num

noncomputable def pathValue (t : ℝ) : ℝ := (1 + t) * (1 + (1 - t) ^ 2 / 4) ^ 2

theorem path_feasible {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Constraint ((1 - t) / 2) (Real.sqrt t) ((1 - t) / 2) := by
  refine ⟨by linarith [ht.2], Real.sqrt_nonneg _, by linarith [ht.2], ?_⟩
  rw [Real.sq_sqrt ht.1]
  ring

theorem path_value {t : ℝ} (ht : 0 ≤ t) :
    value ((1 - t) / 2) (Real.sqrt t) ((1 - t) / 2) = pathValue t := by
  unfold value pathValue
  rw [Real.sq_sqrt ht]
  ring

theorem path_continuous : Continuous pathValue := by
  unfold pathValue
  fun_prop

theorem path_endpoints : pathValue 0 = 25 / 16 ∧ pathValue 1 = 2 := by
  constructor <;> unfold pathValue <;> ring

theorem attains {z : ℝ} (hz : z ∈ Set.Icc (25 / 16 : ℝ) 2) :
    ∃ a b c : ℝ, Constraint a b c ∧ value a b c = z := by
  have hz' : z ∈ Set.Icc (pathValue 0) (pathValue 1) := by
    simpa only [path_endpoints.1, path_endpoints.2] using hz
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    path_continuous.continuousOn hz'
  exact ⟨(1 - t) / 2, Real.sqrt t, (1 - t) / 2,
    path_feasible ht, (path_value ht.1).trans he⟩

theorem attained_range :
    {z : ℝ | ∃ a b c : ℝ, Constraint a b c ∧ value a b c = z} = Set.Icc (25 / 16) 2 := by
  ext z
  constructor
  · rintro ⟨a, b, c, h, rfl⟩
    exact bounds h
  · exact attains

theorem least_value : IsLeast
    {z : ℝ | ∃ a b c : ℝ, Constraint a b c ∧ value a b c = z} (25 / 16) := by
  rw [attained_range]
  exact ⟨by norm_num, fun _ h => h.1⟩

theorem greatest_value : IsGreatest
    {z : ℝ | ∃ a b c : ℝ, Constraint a b c ∧ value a b c = z} 2 := by
  rw [attained_range]
  exact ⟨by norm_num, fun _ h => h.2⟩

end MixedQuadraticSimplexRange

theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0)
    (hab : a + b ^ 2 + c = 1) :
    (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) ≥ 25 / 16 ∧
      (a = 1 / 2 ∧ b = 0 ∧ c = 1 / 2) →
      (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) = 25 / 16 := by
  intro h
  exact (MixedQuadraticSimplexRange.lower_equality ⟨ha, hb, hc, hab⟩).mpr h.2

#print axioms MixedQuadraticSimplexRange.Constraint
#print axioms MixedQuadraticSimplexRange.value
#print axioms MixedQuadraticSimplexRange.reduced
#print axioms MixedQuadraticSimplexRange.gapFactor
#print axioms MixedQuadraticSimplexRange.reduction
#print axioms MixedQuadraticSimplexRange.parameters
#print axioms MixedQuadraticSimplexRange.gap_factor_pos
#print axioms MixedQuadraticSimplexRange.coefficient_bounds
#print axioms MixedQuadraticSimplexRange.lower_gap
#print axioms MixedQuadraticSimplexRange.upper_gap
#print axioms MixedQuadraticSimplexRange.reduced_bounds
#print axioms MixedQuadraticSimplexRange.reduced_lower_equality
#print axioms MixedQuadraticSimplexRange.reduced_upper_equality
#print axioms MixedQuadraticSimplexRange.bounds
#print axioms MixedQuadraticSimplexRange.lower_equality
#print axioms MixedQuadraticSimplexRange.upper_equality
#print axioms MixedQuadraticSimplexRange.pathValue
#print axioms MixedQuadraticSimplexRange.path_feasible
#print axioms MixedQuadraticSimplexRange.path_value
#print axioms MixedQuadraticSimplexRange.path_continuous
#print axioms MixedQuadraticSimplexRange.path_endpoints
#print axioms MixedQuadraticSimplexRange.attains
#print axioms MixedQuadraticSimplexRange.attained_range
#print axioms MixedQuadraticSimplexRange.least_value
#print axioms MixedQuadraticSimplexRange.greatest_value
#print axioms solution
