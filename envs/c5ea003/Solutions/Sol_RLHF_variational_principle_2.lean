-- Prove2me | solution 2 for RLHF.variational_principle
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:17:36.507066+00:00
-- url     : https://prove2.me/submissions/f8252b1c-5068-4f2c-8dca-a330cc614aed

import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
open RLHF Finset in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] {β : ℝ} {r p q : Ω → ℝ} (hβ : 0 < β)
    (hp : IsPosDist p) (hq : IsDist q) :
    objective β r p q ≤ β * Real.log (partition β r p) := by
  obtain ⟨hppos, hpsum⟩ := hp
  obtain ⟨hqnn, hqsum⟩ := hq
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  -- the partition function is positive
  have hZpos : 0 < partition β r p := by
    show 0 < ∑ y, p y * Real.exp (r y / β)
    exact Finset.sum_pos (fun y _ => mul_pos (hppos y) (Real.exp_pos _)) Finset.univ_nonempty
  set Z := partition β r p with hZ
  -- the Gibbs policy `π y = p y e^{r y / β} / Z` is a strictly positive distribution
  set pi : Ω → ℝ := fun y => p y * Real.exp (r y / β) / Z with hpi
  have hpipos : ∀ y, 0 < pi y := fun y =>
    div_pos (mul_pos (hppos y) (Real.exp_pos _)) hZpos
  have hpisum : ∑ y, pi y = 1 := by
    simp only [hpi]
    rw [← Finset.sum_div]
    exact div_self hZpos.ne'
  -- Gibbs' inequality at `(q, pi)`
  have hkl : 0 ≤ klDiv q pi := by
    show (0 : ℝ) ≤ ∑ y, q y * Real.log (q y / pi y)
    have key : ∀ y : Ω, q y - pi y ≤ q y * Real.log (q y / pi y) := by
      intro y
      rcases eq_or_lt_of_le (hqnn y) with h0 | hpos
      · rw [← h0]
        have hpy := hpipos y
        have hz : (0 : ℝ) * Real.log (0 / pi y) = 0 := by ring
        rw [hz]
        linarith
      · have hpy := hpipos y
        have hratio : 0 < pi y / q y := div_pos hpy hpos
        have hlog := Real.log_le_sub_one_of_pos hratio
        have hinv : Real.log (q y / pi y) = -Real.log (pi y / q y) := by
          rw [← Real.log_inv]
          congr 1
          field_simp
        have hmul : q y * Real.log (pi y / q y) ≤ q y * (pi y / q y - 1) :=
          mul_le_mul_of_nonneg_left hlog hpos.le
        have hcancel : q y * (pi y / q y - 1) = pi y - q y := by field_simp
        rw [hinv]
        nlinarith [hmul, hcancel]
    calc (0 : ℝ) = (∑ y, q y) - ∑ y, pi y := by rw [hqsum, hpisum]; ring
      _ = ∑ y, (q y - pi y) := (Finset.sum_sub_distrib _ _).symm
      _ ≤ ∑ y, q y * Real.log (q y / pi y) := Finset.sum_le_sum fun y _ => key y
  -- change of measure: `KL(q‖π) = KL(q‖p) + log Z - 𝔼_q r / β`
  have hlogsplit : ∀ y : Ω, 0 < q y →
      Real.log (q y / pi y) = Real.log (q y / p y) + Real.log Z - r y / β := by
    intro y hqy
    have hpy := hppos y
    have he : (0 : ℝ) < Real.exp (r y / β) := Real.exp_pos _
    have hrw : q y / pi y = q y * Z / (p y * Real.exp (r y / β)) := by
      simp only [hpi]
      rw [div_div_eq_mul_div]
    rw [hrw, Real.log_div (mul_pos hqy hZpos).ne' (mul_pos hpy he).ne',
      Real.log_mul hqy.ne' hZpos.ne', Real.log_mul hpy.ne' he.ne', Real.log_exp,
      Real.log_div hqy.ne' hpy.ne']
    ring
  have hterm : ∀ y : Ω, q y * Real.log (q y / pi y)
      = q y * Real.log (q y / p y) + q y * Real.log Z - q y * r y / β := by
    intro y
    rcases eq_or_lt_of_le (hqnn y) with h0 | hqy
    · rw [← h0]; ring
    · rw [hlogsplit y hqy]; ring
  have hid : klDiv q pi = klDiv q p + Real.log Z - (∑ y, q y * r y) / β := by
    show ∑ y, q y * Real.log (q y / pi y) = klDiv q p + Real.log Z - (∑ y, q y * r y) / β
    calc ∑ y, q y * Real.log (q y / pi y)
        = ∑ y, (q y * Real.log (q y / p y) + q y * Real.log Z - q y * r y / β) :=
          Finset.sum_congr rfl fun y _ => hterm y
      _ = (∑ y, (q y * Real.log (q y / p y) + q y * Real.log Z))
            - ∑ y, q y * r y / β := Finset.sum_sub_distrib _ _
      _ = ((∑ y, q y * Real.log (q y / p y)) + ∑ y, q y * Real.log Z)
            - ∑ y, q y * r y / β := by rw [Finset.sum_add_distrib]
      _ = klDiv q p + Real.log Z - (∑ y, q y * r y) / β := by
            rw [← Finset.sum_mul, hqsum, one_mul, ← Finset.sum_div]
            rfl
  -- conclude: the slack is exactly `β · KL(q‖π) ≥ 0`
  show (∑ y, q y * r y) - β * klDiv q p ≤ β * Real.log Z
  have hβkl : 0 ≤ β * klDiv q pi := mul_nonneg hβ.le hkl
  rw [hid] at hβkl
  have hexp : β * (klDiv q p + Real.log Z - (∑ y, q y * r y) / β)
      = β * klDiv q p + β * Real.log Z - ∑ y, q y * r y := by
    field_simp
  rw [hexp] at hβkl
  linarith
