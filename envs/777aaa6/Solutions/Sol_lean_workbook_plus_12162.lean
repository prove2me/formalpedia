-- Prove2me | solution 1 for lean_workbook_plus_12162
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:42:13.46978+00:00
-- url     : https://prove2.me/submissions/6bb99917-3abd-4295-9404-93fc9557cb4f

import Mathlib

namespace PositiveQuadraticThresholdPairs

theorem threshold {k x y : ℕ} (hk : 0 < k) :
    y ^ 2 < k * x ↔ y ^ 2 / k + 1 ≤ x := by
  rw [Nat.mul_comm k x, ← Nat.div_lt_iff_lt_mul hk]
  omega

theorem natural_classification {k x y : ℕ} (hk : 0 < k) :
    (0 < x ∧ 0 < y ∧ y ^ 2 < k * x) ↔
      ∃ t : ℕ, 0 < y ∧ x = y ^ 2 / k + 1 + t := by
  constructor
  · rintro ⟨_, hy, hb⟩
    have h := (threshold hk).mp hb
    exact ⟨x - (y ^ 2 / k + 1), hy, by omega⟩
  · rintro ⟨t, hy, rfl⟩
    exact ⟨by positivity, hy, (threshold hk).mpr (by omega)⟩

theorem unique_parameter {k x y : ℕ} (hk : 0 < k) (hb : y ^ 2 < k * x) :
    ∃! t : ℕ, x = y ^ 2 / k + 1 + t := by
  have h := (threshold hk).mp hb
  refine ⟨x - (y ^ 2 / k + 1), by omega, ?_⟩
  intro t ht
  omega

theorem integer_classification {k : ℕ} (hk : 0 < k) (x y : ℤ) :
    (0 < x ∧ 0 < y ∧ y ^ 2 < (k : ℤ) * x) ↔
      ∃ u t : ℕ, 0 < u ∧ y = u ∧ x = (u ^ 2 / k + 1 + t : ℕ) := by
  constructor
  · rintro ⟨hx, hy, hb⟩
    have hxc : (x.toNat : ℤ) = x := Int.toNat_of_nonneg (by omega)
    have hyc : (y.toNat : ℤ) = y := Int.toNat_of_nonneg (by omega)
    have hxn : 0 < x.toNat := by omega
    have hyn : 0 < y.toNat := by omega
    have hn : y.toNat ^ 2 < k * x.toNat := by
      exact_mod_cast (show (y.toNat : ℤ) ^ 2 < (k : ℤ) * x.toNat by
        simpa only [hxc, hyc] using hb)
    obtain ⟨t, _, ht⟩ := (natural_classification hk).mp ⟨hxn, hyn, hn⟩
    exact ⟨y.toNat, t, hyn, hyc.symm, by rw [← hxc, ht]⟩
  · rintro ⟨u, t, hu, rfl, rfl⟩
    have hn := (natural_classification hk).mpr ⟨t, hu, rfl⟩
    exact_mod_cast hn

theorem square_fiber {k x y : ℕ} (hk : 0 < k) (hx : 0 < x) :
    y ^ 2 < k * x ↔ y ≤ Nat.sqrt (k * x - 1) := by
  rw [Nat.le_sqrt']
  have hp := Nat.mul_pos hk hx
  omega

def fiber (k x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (k * x)).filter (fun y => y ^ 2 < k * x)

theorem mem_fiber {k x y : ℕ} :
    y ∈ fiber k x ↔ 0 < y ∧ y ^ 2 < k * x := by
  simp only [fiber, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hy, _⟩, hb⟩
    exact ⟨by omega, hb⟩
  · rintro ⟨hy, hb⟩
    have hys : y ≤ y ^ 2 := by nlinarith
    exact ⟨⟨by omega, by omega⟩, hb⟩

theorem fiber_eq {k x : ℕ} (hk : 0 < k) (hx : 0 < x) :
    fiber k x = Finset.Icc 1 (Nat.sqrt (k * x - 1)) := by
  ext y
  rw [mem_fiber, square_fiber hk hx, Finset.mem_Icc]
  omega

theorem fiber_card {k x : ℕ} (hk : 0 < k) (hx : 0 < x) :
    (fiber k x).card = Nat.sqrt (k * x - 1) := by
  rw [fiber_eq hk hx, Nat.card_Icc]
  omega

theorem fiber_zero (k : ℕ) : fiber k 0 = ∅ := by
  simp [fiber]

def box (k X : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Icc 1 X).sigma (fiber k)

theorem mem_box {k X : ℕ} {p : Σ _ : ℕ, ℕ} :
    p ∈ box k X ↔ 0 < p.1 ∧ p.1 ≤ X ∧ 0 < p.2 ∧ p.2 ^ 2 < k * p.1 := by
  simp only [box, Finset.mem_sigma, Finset.mem_Icc, mem_fiber]
  omega

theorem box_card {k : ℕ} (hk : 0 < k) (X : ℕ) :
    (box k X).card = ∑ x ∈ Finset.Icc 1 X, Nat.sqrt (k * x - 1) := by
  rw [box, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro x hx
  exact fiber_card hk (by have := (Finset.mem_Icc.mp hx).1; omega)

theorem unbounded_models {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ∃ x y : ℕ, 0 < x ∧ N < y ∧ y ^ 2 < k * x := by
  refine ⟨(N + 1) ^ 2 / k + 1, N + 1, by positivity, by omega, ?_⟩
  exact (threshold hk).mpr (by omega)

theorem source (x y : ℤ) :
    (0 < x ∧ 0 < y ∧ 0 < 11 * x - y ^ 2) ↔
      ∃ u t : ℕ, 0 < u ∧ y = u ∧ x = (u ^ 2 / 11 + 1 + t : ℕ) := by
  have h := integer_classification (by norm_num : 0 < (11 : ℕ)) x y
  norm_num only [Nat.cast_ofNat] at h
  constructor
  · rintro ⟨hx, hy, hb⟩
    exact h.mp ⟨hx, hy, by linarith⟩
  · intro he
    obtain ⟨hx, hy, hb⟩ := h.mpr he
    exact ⟨hx, hy, by linarith⟩

theorem source_fiber (x : ℕ) (hx : 0 < x) :
    fiber 11 x = Finset.Icc 1 (Nat.sqrt (11 * x - 1)) ∧
      (fiber 11 x).card = Nat.sqrt (11 * x - 1) :=
  ⟨fiber_eq (by norm_num) hx, fiber_card (by norm_num) hx⟩

end PositiveQuadraticThresholdPairs

theorem solution (x y : ℤ) (h₁ : 0 < x ∧ 0 < y) (h₂ : 11 * x - y ^ 2 > 0) :
    ∃ x y : ℤ, 0 < x ∧ 0 < y ∧ 11 * x - y ^ 2 > 0 := by
  obtain ⟨u, t, hu, hy, hx⟩ :=
    (PositiveQuadraticThresholdPairs.source x y).mp ⟨h₁.1, h₁.2, h₂⟩
  exact ⟨x, y, (PositiveQuadraticThresholdPairs.source x y).mpr ⟨u, t, hu, hy, hx⟩⟩

#print axioms PositiveQuadraticThresholdPairs.threshold
#print axioms PositiveQuadraticThresholdPairs.natural_classification
#print axioms PositiveQuadraticThresholdPairs.unique_parameter
#print axioms PositiveQuadraticThresholdPairs.integer_classification
#print axioms PositiveQuadraticThresholdPairs.square_fiber
#print axioms PositiveQuadraticThresholdPairs.fiber
#print axioms PositiveQuadraticThresholdPairs.mem_fiber
#print axioms PositiveQuadraticThresholdPairs.fiber_eq
#print axioms PositiveQuadraticThresholdPairs.fiber_card
#print axioms PositiveQuadraticThresholdPairs.fiber_zero
#print axioms PositiveQuadraticThresholdPairs.box
#print axioms PositiveQuadraticThresholdPairs.mem_box
#print axioms PositiveQuadraticThresholdPairs.box_card
#print axioms PositiveQuadraticThresholdPairs.unbounded_models
#print axioms PositiveQuadraticThresholdPairs.source
#print axioms PositiveQuadraticThresholdPairs.source_fiber
#print axioms solution
