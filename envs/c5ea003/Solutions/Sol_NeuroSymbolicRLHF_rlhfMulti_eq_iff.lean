-- Prove2me | solution 1 for NeuroSymbolicRLHF.rlhfMulti_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T16:58:26.395628+00:00
-- url     : https://prove2.me/submissions/39629f18-45bc-4895-8d5a-c73ba9e60ac6

import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFMultiPrompt
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
open NeuroSymbolicRLHF Finset in
theorem solution {ι : Type*} [Fintype ι] {χ : Type*} [Fintype χ] {β : ℝ} (hβ : 0 < β)
    {D : χ → ℝ} {ref r p : χ → ι → ℝ} [Nonempty ι]
    (hD : ∀ x, 0 < D x) (href : ∀ x, IsPosProb (ref x)) (hp : ∀ x, IsProb (p x)) :
    rlhfMulti β D ref r p = freeEnergyMulti β D ref r
      ↔ ∀ x, p x = gibbs β (ref x) (r x) := by
  -- Gibbs' inequality, termwise: `q log (q/p) ≥ q − p`, with equality only when `q = p`
  have hterm : ∀ a b : ℝ, 0 ≤ a → 0 < b → a - b ≤ a * Real.log (a / b) := by
    intro a b ha hb
    rcases ha.eq_or_lt with h | h
    · subst h
      simp only [zero_sub, zero_div, Real.log_zero, mul_zero]
      linarith
    · have h1 := Real.log_le_sub_one_of_pos (div_pos hb h)
      have h2 : Real.log (a / b) = -Real.log (b / a) := by
        rw [← Real.log_inv, inv_div]
      rw [h2]
      have h3 : a * (b / a - 1) = b - a := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left h1 h.le]
  have hstrict : ∀ a b : ℝ, 0 < a → 0 < b → a ≠ b → a - b < a * Real.log (a / b) := by
    intro a b ha hb hab
    have hne : b / a ≠ 1 := by
      intro h
      apply hab
      field_simp at h
      linarith
    have h1 := Real.log_lt_sub_one_of_pos (div_pos hb ha) hne
    have h2 : Real.log (a / b) = -Real.log (b / a) := by
      rw [← Real.log_inv, inv_div]
    rw [h2]
    have h3 : a * (b / a - 1) = b - a := by field_simp
    nlinarith [mul_lt_mul_of_pos_left h1 ha]
  have hkl : ∀ (q p : ι → ℝ), IsProb q → IsPosProb p →
      0 ≤ klDivFin q p ∧ (klDivFin q p = 0 → q = p) := by
    intro q p hq hp
    have hsum : ∑ y, (q y * Real.log (q y / p y) - (q y - p y)) = klDivFin q p := by
      unfold klDivFin
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hq.sum_one, hp.sum_one, sub_self, sub_zero]
    have hnn : ∀ y, 0 ≤ q y * Real.log (q y / p y) - (q y - p y) := fun y => by
      linarith [hterm (q y) (p y) (hq.nonneg y) (hp.pos y)]
    refine ⟨?_, fun h0 => ?_⟩
    · rw [← hsum]
      exact Finset.sum_nonneg (fun y _ => hnn y)
    · have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hnn y)).mp (hsum.trans h0)
      funext y
      have hy := hz y (Finset.mem_univ y)
      rcases (hq.nonneg y).eq_or_lt with h | h
      · have hp0 : p y = 0 := by
          rw [← h] at hy
          simpa using hy
        exact absurd hp0 (hp.pos y).ne'
      · by_contra hne
        have := hstrict (q y) (p y) h (hp.pos y) hne
        linarith
  -- Gibbs variational identity: `Obj(q) = F − β KL(q ‖ π)` for every distribution `q`
  have hvar : ∀ (rf rw q : ι → ℝ), IsPosProb rf → IsProb q →
      rlhfObj β rf rw q = freeEnergy β rf rw - β * klDivFin q (gibbs β rf rw) := by
    intro rf rw q hrf hq
    have hZ : 0 < tiltZ β rf rw :=
      sum_pos (fun i _ => mul_pos (hrf.pos i) (Real.exp_pos _)) univ_nonempty
    have hid : ∀ y, q y * Real.log (q y / rf y)
        = q y * Real.log (q y / gibbs β rf rw y) + q y * (rw y / β)
          - q y * Real.log (tiltZ β rf rw) := by
      intro y
      rcases (hq.nonneg y).eq_or_lt with h | h
      · rw [← h]
        ring
      · have hπy : gibbs β rf rw y = rf y * Real.exp (rw y / β) / tiltZ β rf rw := rfl
        rw [hπy, Real.log_div h.ne' (hrf.pos y).ne',
          Real.log_div h.ne' (div_pos (mul_pos (hrf.pos y) (Real.exp_pos _)) hZ).ne',
          Real.log_div (mul_pos (hrf.pos y) (Real.exp_pos _)).ne' hZ.ne',
          Real.log_mul (hrf.pos y).ne' (Real.exp_pos _).ne', Real.log_exp]
        ring
    unfold rlhfObj klDivFin freeEnergy
    simp only [hid, sum_sub_distrib, sum_add_distrib, ← sum_mul, hq.sum_one, one_mul]
    have hr : ∑ y, q y * (rw y / β) = (∑ y, q y * rw y) / β := by
      rw [sum_div]
      exact sum_congr rfl (fun y _ => by ring)
    rw [hr]
    field_simp
    ring
  -- the Gibbs policy is a positive distribution
  have hgpos : ∀ x, IsPosProb (gibbs β (ref x) (r x)) := by
    intro x
    have hZ : 0 < tiltZ β (ref x) (r x) :=
      sum_pos (fun i _ => mul_pos ((href x).pos i) (Real.exp_pos _)) univ_nonempty
    refine ⟨fun i => div_pos (mul_pos ((href x).pos i) (Real.exp_pos _)) hZ, ?_⟩
    unfold gibbs
    rw [← sum_div]
    exact div_self hZ.ne'
  -- the objective splits as `Σ D F − β Σ D KL`
  have hsplit : rlhfMulti β D ref r p
      = freeEnergyMulti β D ref r - β * ∑ x, D x * klDivFin (p x) (gibbs β (ref x) (r x)) := by
    unfold rlhfMulti freeEnergyMulti
    simp only [hvar _ _ _ (href _) (hp _), mul_sub, sum_sub_distrib, mul_sum]
    congr 1
    exact sum_congr rfl (fun x _ => by ring)
  have hklnn : ∀ x, 0 ≤ klDivFin (p x) (gibbs β (ref x) (r x)) := fun x =>
    (hkl (p x) _ (hp x) (hgpos x)).1
  rw [hsplit]
  constructor
  · intro h x
    have hsum : ∑ x, D x * klDivFin (p x) (gibbs β (ref x) (r x)) = 0 := by
      have : β * ∑ x, D x * klDivFin (p x) (gibbs β (ref x) (r x)) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hβ.ne'
    have hz := (sum_eq_zero_iff_of_nonneg (fun x _ => mul_nonneg (hD x).le (hklnn x))).mp hsum x
      (mem_univ x)
    have hkx : klDivFin (p x) (gibbs β (ref x) (r x)) = 0 :=
      (mul_eq_zero.mp hz).resolve_left (hD x).ne'
    exact (hkl (p x) _ (hp x) (hgpos x)).2 hkx
  · intro h
    have hz : ∑ x, D x * klDivFin (p x) (gibbs β (ref x) (r x)) = 0 := by
      refine sum_eq_zero (fun x _ => ?_)
      rw [h x]
      unfold klDivFin
      rw [sum_eq_zero (fun i _ => by rw [div_self ((hgpos x).pos i).ne', Real.log_one, mul_zero]),
        mul_zero]
    rw [hz, mul_zero, sub_zero]
