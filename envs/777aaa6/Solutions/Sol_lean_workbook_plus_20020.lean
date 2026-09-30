-- Prove2me | solution 1 for lean_workbook_plus_20020
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:39:10.407636+00:00
-- url     : https://prove2.me/submissions/ace87675-d01c-49ee-9423-eaa1bfdc2667

import Mathlib

namespace ParameterizedSimplexExtrema

def Simplex (x y z : ℝ) : Prop := 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = 1

def value (k x y z : ℝ) : ℝ := x ^ 2 + y ^ 2 + z ^ 2 + k * x * y * z

noncomputable def centralValue (k : ℝ) : ℝ := 1 / 3 + k / 27

def attainable (k : ℝ) : Set ℝ := {v | ∃ x y z : ℝ, Simplex x y z ∧ value k x y z = v}

theorem schur_ordered (a b c : ℝ) (hc : 0 ≤ c) (hab : b ≤ a) (hbc : c ≤ b) :
    a ^ 2 * (b + c - a) + b ^ 2 * (a + c - b) + c ^ 2 * (a + b - c) ≤
      3 * a * b * c := by
  have h1 := mul_nonneg (sq_nonneg (a - b)) (show 0 ≤ a + b - c by linarith)
  have h2 := mul_nonneg hc
    (mul_nonneg (sub_nonneg.mpr (hbc.trans hab)) (sub_nonneg.mpr hbc))
  nlinarith

theorem schur_nonnegative (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    4 * (a + b + c) * (a * b + b * c + c * a) ≤
      (a + b + c) ^ 3 + 9 * a * b * c := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · nlinarith [schur_ordered c b a ha hbc hab]
    · rcases le_total a c with hac | hca
      · nlinarith [schur_ordered b c a ha hcb hac]
      · nlinarith [schur_ordered b a c hc hab hca]
  · rcases le_total a c with hac | hca
    · nlinarith [schur_ordered c a b hb hac hba]
    · rcases le_total b c with hbc | hcb
      · nlinarith [schur_ordered a c b hb hca hbc]
      · nlinarith [schur_ordered a b c hc hba hcb]

theorem amgm_at_minimum (a b c : ℝ) (hc : 0 ≤ c) (hca : c ≤ a) (hcb : c ≤ b) :
    27 * a * b * c ≤ (a + b + c) ^ 3 := by
  have hp : 0 ≤ a + b - 2 * c := by linarith
  have hq : 0 ≤ (a - c) ^ 2 - (a - c) * (b - c) + (b - c) ^ 2 := by
    nlinarith [sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a - b)]
  have hm := mul_nonneg hc hq
  have h3 := pow_nonneg hp 3
  nlinarith only [hm, h3]

theorem amgm_three (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    27 * a * b * c ≤ (a + b + c) ^ 3 := by
  rcases le_total a b with hab | hba
  · rcases le_total a c with hac | hca
    · nlinarith only [amgm_at_minimum b c a ha hab hac]
    · exact amgm_at_minimum a b c hc hca (hca.trans hab)
  · rcases le_total b c with hbc | hcb
    · nlinarith only [amgm_at_minimum a c b hb hba hbc]
    · exact amgm_at_minimum a b c hc (hcb.trans hba) hcb

theorem product_bounds (x y z : ℝ) (h : Simplex x y z) :
    0 ≤ x * y * z ∧ x * y * z ≤ 1 / 27 := by
  obtain ⟨hx, hy, hz, hs⟩ := h
  have hp := amgm_three x y z hx hy hz
  rw [hs, one_pow] at hp
  exact ⟨mul_nonneg (mul_nonneg hx hy) hz, by linarith⟩

theorem lower_anchor (x y z : ℝ) (h : Simplex x y z) : 1 / 2 ≤ value (9 / 2) x y z := by
  obtain ⟨hx, hy, hz, hs⟩ := h
  have hsch := schur_nonnegative x y z hx hy hz
  simp only [hs, one_pow, mul_one, one_mul] at hsch
  have hs2 : (x + y + z) ^ 2 = 1 := by rw [hs]; ring
  unfold value
  nlinarith only [hs2, hsch]

theorem upper_anchor (x y z : ℝ) (h : Simplex x y z) : value 18 x y z ≤ 1 := by
  obtain ⟨hx, hy, hz, hs⟩ := h
  have h1 := mul_nonneg hx (sq_nonneg (y - z))
  have h2 := mul_nonneg hy (sq_nonneg (z - x))
  have h3 := mul_nonneg hz (sq_nonneg (x - y))
  have hq : 9 * x * y * z ≤ (x + y + z) * (x * y + y * z + z * x) := by
    nlinarith only [h1, h2, h3]
  rw [hs, one_mul] at hq
  have hs2 : (x + y + z) ^ 2 = 1 := by rw [hs]; ring
  unfold value
  nlinarith only [hs2, hq]

theorem sharp_bounds (k x y z : ℝ) (h : Simplex x y z) :
    min (centralValue k) (1 / 2) ≤ value k x y z ∧
      value k x y z ≤ max 1 (centralValue k) := by
  obtain ⟨hp0, hp⟩ := product_bounds x y z h
  have hl := lower_anchor x y z h
  have hu := upper_anchor x y z h
  constructor
  · by_cases hk : k ≤ 9 / 2
    · rw [min_eq_left (show centralValue k ≤ 1 / 2 by unfold centralValue; linarith)]
      have hm := mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hp)
      unfold value centralValue at *
      nlinarith only [hl, hm]
    · rw [min_eq_right (show 1 / 2 ≤ centralValue k by unfold centralValue; linarith)]
      have hm := mul_nonneg (show 0 ≤ k - 9 / 2 by linarith) hp0
      unfold value at *
      nlinarith only [hl, hm]
  · by_cases hk : k ≤ 18
    · rw [max_eq_left (show centralValue k ≤ 1 by unfold centralValue; linarith)]
      have hm := mul_nonneg (sub_nonneg.mpr hk) hp0
      unfold value at *
      nlinarith only [hu, hm]
    · rw [max_eq_right (show 1 ≤ centralValue k by unfold centralValue; linarith)]
      have hm := mul_nonneg (show 0 ≤ k - 18 by linarith) (sub_nonneg.mpr hp)
      unfold value centralValue at *
      nlinarith only [hu, hm]

theorem center_attainment (k : ℝ) : centralValue k ∈ attainable k := by
  refine ⟨1 / 3, 1 / 3, 1 / 3, ⟨by positivity, by positivity, by positivity, by ring⟩, ?_⟩
  unfold value centralValue
  ring

theorem edge_attainment (k : ℝ) : (1 / 2 : ℝ) ∈ attainable k := by
  refine ⟨0, 1 / 2, 1 / 2, ⟨le_rfl, by positivity, by positivity, by ring⟩, ?_⟩
  unfold value
  ring

theorem vertex_attainment (k : ℝ) : (1 : ℝ) ∈ attainable k := by
  refine ⟨1, 0, 0, ⟨by positivity, le_rfl, le_rfl, by ring⟩, ?_⟩
  unfold value
  ring

theorem exact_minimum (k : ℝ) : IsLeast (attainable k) (min (centralValue k) (1 / 2)) := by
  constructor
  · rcases le_total (centralValue k) (1 / 2) with h | h
    · rw [min_eq_left h]
      exact center_attainment k
    · rw [min_eq_right h]
      exact edge_attainment k
  · rintro v ⟨x, y, z, hs, hv⟩
    rw [← hv]
    exact (sharp_bounds k x y z hs).1

theorem exact_maximum (k : ℝ) : IsGreatest (attainable k) (max 1 (centralValue k)) := by
  constructor
  · rcases le_total 1 (centralValue k) with h | h
    · rw [max_eq_right h]
      exact center_attainment k
    · rw [max_eq_left h]
      exact vertex_attainment k
  · rintro v ⟨x, y, z, hs, hv⟩
    rw [← hv]
    exact (sharp_bounds k x y z hs).2

theorem transition_parameters (k : ℝ) :
    (centralValue k ≤ 1 / 2 ↔ k ≤ 9 / 2) ∧ (centralValue k ≤ 1 ↔ k ≤ 18) := by
  unfold centralValue
  constructor <;> constructor <;> intro h <;> linarith

end ParameterizedSimplexExtrema

theorem solution (x y z k : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hs : x + y + z = 1) :
    x ^ 2 + y ^ 2 + z ^ 2 + k * x * y * z ≤ 1 + k / 27 ∨
    x ^ 2 + y ^ 2 + z ^ 2 + k * x * y * z ≥ 1 + k / 27 := le_total _ _

#print axioms ParameterizedSimplexExtrema.schur_ordered
#print axioms ParameterizedSimplexExtrema.schur_nonnegative
#print axioms ParameterizedSimplexExtrema.amgm_at_minimum
#print axioms ParameterizedSimplexExtrema.amgm_three
#print axioms ParameterizedSimplexExtrema.product_bounds
#print axioms ParameterizedSimplexExtrema.lower_anchor
#print axioms ParameterizedSimplexExtrema.upper_anchor
#print axioms ParameterizedSimplexExtrema.sharp_bounds
#print axioms ParameterizedSimplexExtrema.center_attainment
#print axioms ParameterizedSimplexExtrema.edge_attainment
#print axioms ParameterizedSimplexExtrema.vertex_attainment
#print axioms ParameterizedSimplexExtrema.exact_minimum
#print axioms ParameterizedSimplexExtrema.exact_maximum
#print axioms ParameterizedSimplexExtrema.transition_parameters
#print axioms solution
