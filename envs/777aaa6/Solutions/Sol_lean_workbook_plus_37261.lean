-- Prove2me | solution 1 for lean_workbook_plus_37261
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:13:06.210276+00:00
-- url     : https://prove2.me/submissions/a59a85aa-3daa-4604-b665-cda944cf6795

import Mathlib

namespace FourNumberPairingBound

def Constraint (a b c d : ℝ) : Prop :=
  a + b + c + d = 9 ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 21

noncomputable def gap (a b c d : ℝ) : ℝ :=
  max |a * b - c * d| (max |a * c - b * d| |a * d - b * c|)

theorem normalized_product_bound {u v w : ℝ} (h : u ^ 2 + v ^ 2 + w ^ 2 = 3) :
    u * v * w ≤ 1 := by
  have huv : 2 * |u| * |v| ≤ u ^ 2 + v ^ 2 := by
    nlinarith only [sq_nonneg (|u| - |v|), sq_abs u, sq_abs v]
  have hm := mul_le_mul_of_nonneg_right huv (abs_nonneg w)
  have hs : u ^ 2 + v ^ 2 = 3 - w ^ 2 := by linarith
  rw [hs] at hm
  have he : (|w| - 1) ^ 2 * (|w| + 2) = |w| * w ^ 2 - 3 * |w| + 2 := by
    rw [← sq_abs w]
    ring
  have hn := mul_nonneg (sq_nonneg (|w| - 1)) (show 0 ≤ |w| + 2 by positivity)
  have habs : |u * v * w| = |u| * |v| * |w| := by simp only [abs_mul]
  have hb : |u * v * w| ≤ 1 := by nlinarith only [hm, he, hn, habs]
  exact (le_abs_self _).trans hb

theorem normalized_square_certificate (L u v w : ℝ)
    (h : u ^ 2 + v ^ 2 + w ^ 2 = 3) :
    (L * u - v * w) ^ 2 + (L * v - u * w) ^ 2 + (L * w - u * v) ^ 2 -
      3 * (L - 1) ^ 2 =
      (u * v - w) ^ 2 + (u * w - v) ^ 2 + (v * w - u) ^ 2 +
        6 * (L - 1) * (1 - u * v * w) := by
  linear_combination (L ^ 2 - 1) * h

theorem normalized_squared_bound {L u v w : ℝ} (hL : 1 ≤ L)
    (h : u ^ 2 + v ^ 2 + w ^ 2 = 3) :
    3 * (L - 1) ^ 2 ≤
      (L * u - v * w) ^ 2 + (L * v - u * w) ^ 2 + (L * w - u * v) ^ 2 := by
  have hn := mul_nonneg (show 0 ≤ 6 * (L - 1) by linarith)
    (sub_nonneg.mpr (normalized_product_bound h))
  nlinarith only [normalized_square_certificate L u v w h, hn,
    sq_nonneg (u * v - w), sq_nonneg (u * w - v), sq_nonneg (v * w - u)]

theorem squared_bound {a b c d : ℝ} (h : Constraint a b c d) :
    12 ≤ (a * b - c * d) ^ 2 + (a * c - b * d) ^ 2 + (a * d - b * c) ^ 2 := by
  let u := a + b - c - d
  let v := a - b + c - d
  let w := a - b - c + d
  have hn : u ^ 2 + v ^ 2 + w ^ 2 = 3 := by
    dsimp [u, v, w]
    nlinarith only [h.1, h.2, sq_nonneg (a + b + c + d - 9)]
  have hu : 9 * u - v * w = 4 * (a * b - c * d) := by
    dsimp [u, v, w]
    linear_combination -(a + b - c - d) * h.1
  have hv : 9 * v - u * w = 4 * (a * c - b * d) := by
    dsimp [u, v, w]
    linear_combination -(a - b + c - d) * h.1
  have hw : 9 * w - u * v = 4 * (a * d - b * c) := by
    dsimp [u, v, w]
    linear_combination -(a - b - c + d) * h.1
  have hb := normalized_squared_bound (by norm_num : (1 : ℝ) ≤ 9) hn
  rw [hu, hv, hw] at hb
  nlinarith only [hb]

theorem gap_bound {a b c d : ℝ} (h : Constraint a b c d) : 2 ≤ gap a b c d := by
  by_contra hn
  have hg : gap a b c d < 2 := lt_of_not_ge hn
  have ha : |a * b - c * d| < 2 := (le_max_left _ _).trans_lt hg
  have hb : |a * c - b * d| < 2 := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hg
  have hc : |a * d - b * c| < 2 := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hg
  have ha2 := (sq_lt_sq₀ (abs_nonneg (a * b - c * d)) (by norm_num : (0 : ℝ) ≤ 2)).mpr ha
  have hb2 := (sq_lt_sq₀ (abs_nonneg (a * c - b * d)) (by norm_num : (0 : ℝ) ≤ 2)).mpr hb
  have hc2 := (sq_lt_sq₀ (abs_nonneg (a * d - b * c)) (by norm_num : (0 : ℝ) ≤ 2)).mpr hc
  rw [sq_abs] at ha2 hb2 hc2
  nlinarith only [squared_bound h, ha2, hb2, hc2]

theorem oriented_source {a b c d : ℝ} (h : Constraint a b c d) :
    2 ≤ a * b - c * d ∨ 2 ≤ c * d - a * b ∨
      2 ≤ a * c - b * d ∨ 2 ≤ b * d - a * c ∨
      2 ≤ a * d - b * c ∨ 2 ≤ b * c - a * d := by
  have hg := gap_bound h
  unfold gap at hg
  rcases le_max_iff.mp hg with ha | hbc
  · rcases le_abs.mp ha with ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl (by linarith))
  · rcases le_max_iff.mp hbc with hb | hc
    · rcases le_abs.mp hb with hb | hb
      · exact Or.inr (Or.inr (Or.inl hb))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))
    · rcases le_abs.mp hc with hc | hc
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith)))))

noncomputable def rearrangements (a b c d : ℝ) : Finset (ℝ × ℝ × ℝ × ℝ) := by
  classical
  exact {(a, b, c, d), (c, d, a, b), (a, c, b, d),
    (b, d, a, c), (a, d, b, c), (b, c, a, d)}

theorem rearrangements_preserve_constraint {a b c d : ℝ} (h : Constraint a b c d)
    {z : ℝ × ℝ × ℝ × ℝ} (hz : z ∈ rearrangements a b c d) :
    Constraint z.1 z.2.1 z.2.2.1 z.2.2.2 := by
  classical
  simp only [rearrangements, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
    constructor <;> dsimp <;> nlinarith only [h.1, h.2]

theorem source_rearrangement {a b c d : ℝ} (h : Constraint a b c d) :
    ∃ z ∈ rearrangements a b c d, 2 ≤ z.1 * z.2.1 - z.2.2.1 * z.2.2.2 := by
  classical
  rcases oriented_source h with h | h | h | h | h | h
  · exact ⟨(a, b, c, d), by simp [rearrangements], h⟩
  · exact ⟨(c, d, a, b), by simp [rearrangements], h⟩
  · exact ⟨(a, c, b, d), by simp [rearrangements], h⟩
  · exact ⟨(b, d, a, c), by simp [rearrangements], h⟩
  · exact ⟨(a, d, b, c), by simp [rearrangements], h⟩
  · exact ⟨(b, c, a, d), by simp [rearrangements], h⟩

theorem sharp_model : Constraint 3 2 2 2 ∧ gap 3 2 2 2 = 2 := by
  norm_num [Constraint, gap]
  rfl

theorem sharp_coefficient (k : ℝ) :
    (∀ a b c d : ℝ, Constraint a b c d → k ≤ gap a b c d) ↔ k ≤ 2 := by
  constructor
  · intro h
    simpa only [sharp_model.2] using h 3 2 2 2 sharp_model.1
  · intro hk a b c d h
    exact hk.trans (gap_bound h)

theorem least_best_pair_gap : IsLeast
    {z : ℝ | ∃ a b c d : ℝ, Constraint a b c d ∧ gap a b c d = z} 2 := by
  refine ⟨⟨3, 2, 2, 2, sharp_model.1, sharp_model.2⟩, ?_⟩
  rintro z ⟨a, b, c, d, h, rfl⟩
  exact gap_bound h

end FourNumberPairingBound

theorem solution (a b c d : ℝ) (h₁ : a + b + c + d = 9)
    (h₂ : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 21) :
    ∃ a b c d : ℝ, a + b + c + d = 9 ∧
      a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 21 ∧ a * b - c * d ≥ 2 := by
  obtain ⟨z, hz, hb⟩ := FourNumberPairingBound.source_rearrangement ⟨h₁, h₂⟩
  have hc := FourNumberPairingBound.rearrangements_preserve_constraint ⟨h₁, h₂⟩ hz
  exact ⟨z.1, z.2.1, z.2.2.1, z.2.2.2, hc.1, hc.2, hb⟩

#print axioms FourNumberPairingBound.Constraint
#print axioms FourNumberPairingBound.gap
#print axioms FourNumberPairingBound.normalized_product_bound
#print axioms FourNumberPairingBound.normalized_square_certificate
#print axioms FourNumberPairingBound.normalized_squared_bound
#print axioms FourNumberPairingBound.squared_bound
#print axioms FourNumberPairingBound.gap_bound
#print axioms FourNumberPairingBound.oriented_source
#print axioms FourNumberPairingBound.rearrangements
#print axioms FourNumberPairingBound.rearrangements_preserve_constraint
#print axioms FourNumberPairingBound.source_rearrangement
#print axioms FourNumberPairingBound.sharp_model
#print axioms FourNumberPairingBound.sharp_coefficient
#print axioms FourNumberPairingBound.least_best_pair_gap
#print axioms solution
