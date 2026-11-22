-- Prove2me | solution 1 for Erdos390.two_cell_active_measure_exists
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-16T17:47:27.406003+00:00
-- url     : https://prove2.me/submissions/0635b0d1-a7a5-4f4a-b62e-33732894b857

import Mathlib

open scoped BigOperators

/- Finite interpolation in the baseline active-measure realization lemma,
Section 8 of Shouqiao Wang's Erdos 390 paper, pinned at
61325b10bbdc29f4fb5e0618b414b9f2189333ad. -/
private theorem two_cell_constants
    (A B q μ l r cap : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hq : 0 < q)
    (hl : l < μ) (hr : μ < r)
    (hcapA : q ≤ cap * A) (hcapB : q ≤ cap * B) :
    ∃ u v : ℝ, 0 < u ∧ 0 < v ∧ u ≤ cap ∧ v ≤ cap ∧
      A * u + B * v = q ∧ u * (A * l) + v * (B * r) = q * μ := by
  have hd : 0 < r - l := by linarith
  have hleft : 0 < (r - μ) / (r - l) := div_pos (by linarith) hd
  have hright : 0 < (μ - l) / (r - l) := div_pos (by linarith) hd
  have hleftOne : (r - μ) / (r - l) ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hrightOne : (μ - l) / (r - l) ≤ 1 := (div_le_one hd).mpr (by linarith)
  let u := q * ((r - μ) / (r - l)) / A
  let v := q * ((μ - l) / (r - l)) / B
  have hu : 0 < u := div_pos (mul_pos hq hleft) hA
  have hv : 0 < v := div_pos (mul_pos hq hright) hB
  have huq : q * ((r - μ) / (r - l)) ≤ q := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hleftOne hq.le
  have hvq : q * ((μ - l) / (r - l)) ≤ q := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hrightOne hq.le
  refine ⟨u, v, hu, hv, ?_, ?_, ?_, ?_⟩
  · exact (div_le_div_of_nonneg_right huq hA.le).trans ((div_le_iff₀ hA).mpr hcapA)
  · exact (div_le_div_of_nonneg_right hvq hB.le).trans ((div_le_iff₀ hB).mpr hcapB)
  · dsimp [u, v]
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hd] <;> ring
  · dsimp [u, v]
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hd] <;> ring

theorem solution
    (A B : Finset ℕ) (score : ℕ → ℝ) (q μ cap : ℝ)
    (hA : A.Nonempty) (hB : B.Nonempty) (hdisjoint : Disjoint A B)
    (hq : 0 < q)
    (hlower : (∑ a ∈ A, score a) / (A.card : ℝ) < μ)
    (hupper : μ < (∑ a ∈ B, score a) / (B.card : ℝ))
    (hcapA : q ≤ cap * (A.card : ℝ))
    (hcapB : q ≤ cap * (B.card : ℝ)) :
    ∃ x : ℕ → ℝ,
      (∀ a, 0 ≤ x a ∧ x a ≤ cap) ∧
      (∀ a, a ∉ A ∪ B → x a = 0) ∧
      (∑ a ∈ A ∪ B, x a) = q ∧
      (∑ a ∈ A ∪ B, x a * score a) = q * μ ∧
      ∃ u v : ℝ, 0 < u ∧ 0 < v ∧
        (∀ a ∈ A, x a = u) ∧ (∀ a ∈ B, x a = v) := by
  classical
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hBc : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  let l := (∑ a ∈ A, score a) / (A.card : ℝ)
  let r := (∑ a ∈ B, score a) / (B.card : ℝ)
  obtain ⟨u, v, hu, hv, hucap, hvcap, hmass, hmoment⟩ :=
    two_cell_constants A.card B.card q μ l r cap hAc hBc hq hlower hupper hcapA hcapB
  have hsumA : (A.card : ℝ) * l = ∑ a ∈ A, score a := by
    dsimp [l]
    field_simp [ne_of_gt hAc] <;> ring
  have hsumB : (B.card : ℝ) * r = ∑ a ∈ B, score a := by
    dsimp [r]
    field_simp [ne_of_gt hBc] <;> ring
  rw [hsumA, hsumB] at hmoment
  let x : ℕ → ℝ := fun a ↦ if a ∈ A then u else if a ∈ B then v else 0
  have hxA (a : ℕ) (ha : a ∈ A) : x a = u := by simp [x, ha]
  have hxB (a : ℕ) (hb : a ∈ B) : x a = v := by
    have ha : a ∉ A := fun ha ↦ (Finset.disjoint_left.mp hdisjoint) ha hb
    simp [x, ha, hb]
  have hcapNonneg : 0 ≤ cap := hu.le.trans hucap
  have hbounds (a : ℕ) : 0 ≤ x a ∧ x a ≤ cap := by
    by_cases ha : a ∈ A
    · rw [hxA a ha]
      exact ⟨hu.le, hucap⟩
    · by_cases hb : a ∈ B
      · rw [hxB a hb]
        exact ⟨hv.le, hvcap⟩
      · simp only [x, if_neg ha, if_neg hb]
        exact ⟨le_rfl, hcapNonneg⟩
  have hzero (a : ℕ) (ha : a ∉ A ∪ B) : x a = 0 := by
    have hna : a ∉ A := fun h ↦ ha (Finset.mem_union_left B h)
    have hnb : a ∉ B := fun h ↦ ha (Finset.mem_union_right A h)
    simp [x, hna, hnb]
  have hmassA : (∑ a ∈ A, x a) = (A.card : ℝ) * u := by
    calc
      _ = ∑ _a ∈ A, u := Finset.sum_congr rfl hxA
      _ = _ := by simp
  have hmassB : (∑ a ∈ B, x a) = (B.card : ℝ) * v := by
    calc
      _ = ∑ _a ∈ B, v := Finset.sum_congr rfl hxB
      _ = _ := by simp
  have hmomentA : (∑ a ∈ A, x a * score a) = u * ∑ a ∈ A, score a := by
    calc
      _ = ∑ a ∈ A, u * score a := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hxA a ha]
      _ = _ := (Finset.mul_sum A score u).symm
  have hmomentB : (∑ a ∈ B, x a * score a) = v * ∑ a ∈ B, score a := by
    calc
      _ = ∑ a ∈ B, v * score a := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hxB a ha]
      _ = _ := (Finset.mul_sum B score v).symm
  refine ⟨x, hbounds, hzero, ?_, ?_, u, v, hu, hv, hxA, hxB⟩
  · rw [Finset.sum_union hdisjoint, hmassA, hmassB]
    exact hmass
  · rw [Finset.sum_union hdisjoint, hmomentA, hmomentB]
    exact hmoment
