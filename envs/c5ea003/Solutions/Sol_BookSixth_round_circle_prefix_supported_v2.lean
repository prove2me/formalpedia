-- Prove2me | solution 1 for BookSixth.round_circle_prefix_supported_v2
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T06:09:25.82651+00:00
-- url     : https://prove2.me/submissions/3c2283dc-9baa-4714-913a-85577c1d8017

import Mathlib
import Definitions.Def_BookSixth

section Helpers0e
open BookSixth

theorem iso_basic_0e (A B : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hA : Continuous (fun p : ℝ × (Fin 3 → ℝ) => A p.1 p.2))
    (hB : Continuous (fun p : ℝ × (Fin 3 → ℝ) => B p.1 p.2))
    (hAB : ∀ t x, A t (B t x) = x) (hBA : ∀ t x, B t (A t x) = x)
    (h0 : ∀ x, A 0 x = x) :
    ∃ H : ℝ → (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => H p.1 p.2) ∧
      Continuous (fun p : ℝ × (Fin 3 → ℝ) => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧ (∀ x, H 1 x = A 1 x) := by
  refine ⟨fun t =>
    { toFun := A t, invFun := B t, left_inv := hBA t, right_inv := hAB t,
      continuous_toFun := hA.comp (continuous_const.prodMk continuous_id),
      continuous_invFun := hB.comp (continuous_const.prodMk continuous_id) },
    hA, hB, h0, fun x => rfl⟩

/-- Half-turn about the vertical axis through (3/2, 0, *), as an ambient isotopy. -/
theorem halfturn_0e :
    ∃ H : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => H p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (∀ x, H 1 x = ![3 - x 0, -x 1, x 2]) := by
  obtain ⟨H, h1, h2, h3, h4⟩ := iso_basic_0e
    (fun t x => ![3/2 + Real.cos (t * Real.pi) * (x 0 - 3/2) - Real.sin (t * Real.pi) * x 1,
                  Real.sin (t * Real.pi) * (x 0 - 3/2) + Real.cos (t * Real.pi) * x 1, x 2])
    (fun t x => ![3/2 + Real.cos (t * Real.pi) * (x 0 - 3/2) + Real.sin (t * Real.pi) * x 1,
                  -(Real.sin (t * Real.pi) * (x 0 - 3/2)) + Real.cos (t * Real.pi) * x 1, x 2])
    (by fun_prop) (by fun_prop)
    (by
      intro t x
      funext i
      fin_cases i <;> simp
      · linear_combination (x 0 - 3/2) * Real.cos_sq_add_sin_sq (t * Real.pi)
      · linear_combination x 1 * Real.cos_sq_add_sin_sq (t * Real.pi))
    (by
      intro t x
      funext i
      fin_cases i <;> simp
      · linear_combination (x 0 - 3/2) * Real.cos_sq_add_sin_sq (t * Real.pi)
      · linear_combination x 1 * Real.cos_sq_add_sin_sq (t * Real.pi))
    (by
      intro x
      funext i
      fin_cases i <;> simp)
  refine ⟨H, h1, h2, h3, fun x => ?_⟩
  rw [h4]
  funext i
  fin_cases i <;> simp <;> ring

theorem sc0_image_0e : (fun x : Space3 => ![3 - x 0, -x 1, x 2]) '' standardCircle 0 = standardCircle 1 := by
  unfold standardCircle
  rw [← Set.range_comp]
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t + Real.pi, ?_⟩
    funext i
    fin_cases i <;> simp [Real.cos_add_pi, Real.sin_add_pi] <;> ring
  · rintro ⟨t, rfl⟩
    refine ⟨t + Real.pi, ?_⟩
    funext i
    fin_cases i <;> simp [Real.cos_add_pi, Real.sin_add_pi] <;> ring

theorem sc1_image_0e : (fun x : Space3 => ![3 - x 0, -x 1, x 2]) '' standardCircle 1 = standardCircle 0 := by
  unfold standardCircle
  rw [← Set.range_comp]
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t + Real.pi, ?_⟩
    funext i
    fin_cases i <;> simp [Real.cos_add_pi, Real.sin_add_pi] <;> ring
  · rintro ⟨t, rfl⟩
    refine ⟨t + Real.pi, ?_⟩
    funext i
    fin_cases i <;> simp [Real.cos_add_pi, Real.sin_add_pi] <;> ring

theorem round_sc_0e (k : ℕ) : RoundCircle (standardCircle k) := by
  refine ⟨![3 * (k : ℝ), 0, 0], ![1, 0, 0], ![0, 1, 0], 1, one_pos, ?_, ?_, ?_, ?_⟩
  · simp [Fin.sum_univ_three]
  · simp [Fin.sum_univ_three]
  · simp [Fin.sum_univ_three]
  · unfold standardCircle
    congr 1
    funext t
    funext i
    fin_cases i <;> simp

theorem disj_sc10_0e : Disjoint (standardCircle 1) (standardCircle 0) := by
  rw [Set.disjoint_left]
  rintro x ⟨s, rfl⟩ ⟨t, ht⟩
  have h := congrFun ht 0
  simp at h
  linarith [Real.neg_one_le_cos s, Real.cos_le_one t]

end Helpers0e

set_option maxHeartbeats 4000000 in
open BookSixth in
theorem solution : ¬ (∀ {n : ℕ}
    (C : Fin n → Set Space3) (D : Set Space3)
    (hroundC : ∀ i, RoundCircle (C i)) (hroundD : RoundCircle D)
    (hdisjointC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hdisjointD : ∀ i, Disjoint (C i) D)
    (hprefix : IsUnlink C)
    (hpairs : ∀ i, IsUnlink (![C i, D] : Fin 2 → Set Space3)),
    ∃ K : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x) ∧
      (∀ i, (K 1) '' C i = standardCircle i.val) ∧
      (∀ t, K t '' D = D)) := by
  intro h
  obtain ⟨H, hc1, hc2, h0, h1⟩ := halfturn_0e
  have hH1 : ∀ S : Set Space3, (H 1) '' S = (fun x : Space3 => ![3 - x 0, -x 1, x 2]) '' S := by
    intro S
    exact Set.image_congr (fun x _ => h1 x)
  obtain ⟨K, -, -, -, hK1, hKD⟩ := h (n := 1) (fun _ => standardCircle 1) (standardCircle 0)
    (fun _ => round_sc_0e 1) (round_sc_0e 0)
    (fun i j hij => absurd (Subsingleton.elim i j) hij)
    (fun _ => disj_sc10_0e)
    ⟨H, hc1, hc2, h0, fun i => by
      rw [hH1, sc1_image_0e]
      have : i.val = 0 := by omega
      rw [this]⟩
    (fun _ => ⟨H, hc1, hc2, h0, fun i => by
      fin_cases i
      · change (H 1) '' standardCircle 1 = standardCircle 0
        rw [hH1, sc1_image_0e]
      · change (H 1) '' standardCircle 0 = standardCircle 1
        rw [hH1, sc0_image_0e]⟩)
  have e1 := hK1 0
  have e2 := hKD 1
  simp only [Fin.val_zero] at e1
  have heq : (K 1) '' standardCircle 1 = (K 1) '' standardCircle 0 := by rw [e1, e2]
  have := (Set.image_injective.mpr (K 1).injective) heq
  have hd := disj_sc10_0e
  rw [this, disjoint_self, Set.bot_eq_empty] at hd
  have hmem : (![3 * ((0 : ℕ) : ℝ) + Real.cos 0, Real.sin 0, 0] : Space3) ∈ standardCircle 0 := ⟨0, rfl⟩
  rw [hd] at hmem
  exact hmem
