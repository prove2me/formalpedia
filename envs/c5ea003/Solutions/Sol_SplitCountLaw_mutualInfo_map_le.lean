-- Prove2me | solution 1 for SplitCountLaw.mutualInfo_map_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T06:14:31.524289+00:00
-- url     : https://prove2.me/submissions/1701a2af-54f4-46bd-8827-82136c7b30ad

import Mathlib
import Definitions.Def_Novelty_SplitCountLaw

open SplitCountLaw Finset in
theorem solution {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq γ]
    (p : α → β → ℝ) (g : β → γ)
    (hp : ∀ a b, 0 ≤ p a b) (hrow : ∀ a, 0 < rowMarg p a) (hcol : ∀ b, 0 < colMarg p b) :
    mutualInfo (push p g) ≤ mutualInfo p := by
  set q := push p g with hqdef
  -- marginals of the pushed table
  have hrowq : ∀ a, rowMarg q a = rowMarg p a := by
    intro a
    simp only [rowMarg, hqdef, push]
    exact Finset.sum_fiberwise univ g (p a)
  have hq_ge : ∀ a b, p a b ≤ q a (g b) := by
    intro a b
    simp only [hqdef, push]
    exact single_le_sum (fun b' _ => hp a b') (by simp)
  have hC_ge : ∀ b, colMarg p b ≤ colMarg q (g b) := by
    intro b
    simp only [colMarg]
    exact sum_le_sum fun a _ => hq_ge a b
  have hCpos : ∀ b, 0 < colMarg q (g b) := fun b => lt_of_lt_of_le (hcol b) (hC_ge b)
  -- rewrite `I(q)` as a sum over the original cells
  have hIq : mutualInfo q = ∑ a, ∑ b, p a b *
      Real.logb 2 (q a (g b) / (rowMarg p a * colMarg q (g b))) := by
    unfold mutualInfo
    refine sum_congr rfl fun a _ => ?_
    rw [hrowq a]
    have h1 : ∀ c, q a c * Real.logb 2 (q a c / (rowMarg p a * colMarg q c))
        = ∑ b ∈ univ.filter (fun b => g b = c),
            p a b * Real.logb 2 (q a (g b) / (rowMarg p a * colMarg q (g b))) := by
      intro c
      have hqc : q a c = ∑ b ∈ univ.filter (fun b => g b = c), p a b := rfl
      nth_rewrite 1 [hqc]
      rw [sum_mul]
      refine sum_congr rfl fun b hb => ?_
      rw [(mem_filter.1 hb).2]
    rw [sum_congr rfl fun c _ => h1 c]
    exact Finset.sum_fiberwise univ g
      (fun b => p a b * Real.logb 2 (q a (g b) / (rowMarg p a * colMarg q (g b))))
  -- Gibbs: each cell loses at most `w - p` with `w = c_b q(a, g b) / C_{g b}`
  have hterm : ∀ a b, p a b * (Real.log (q a (g b) / (rowMarg p a * colMarg q (g b)))
      - Real.log (p a b / (rowMarg p a * colMarg p b)))
      ≤ colMarg p b * q a (g b) / colMarg q (g b) - p a b := by
    intro a b
    have hr := hrow a
    have hc := hcol b
    have hC := hCpos b
    rcases (hp a b).eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul, sub_zero]
      have hq0 : 0 ≤ q a (g b) := le_trans (hp a b) (hq_ge a b)
      positivity
    · have hq := lt_of_lt_of_le hpos (hq_ge a b)
      have e : Real.log (q a (g b) / (rowMarg p a * colMarg q (g b)))
          - Real.log (p a b / (rowMarg p a * colMarg p b))
          = Real.log (colMarg p b * q a (g b) / colMarg q (g b) / p a b) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        congr 1
        field_simp
      rw [e]
      have hw : 0 < colMarg p b * q a (g b) / colMarg q (g b) := by positivity
      have h1 := Real.log_le_sub_one_of_pos (div_pos hw hpos)
      calc p a b * Real.log (colMarg p b * q a (g b) / colMarg q (g b) / p a b)
          ≤ p a b * (colMarg p b * q a (g b) / colMarg q (g b) / p a b - 1) :=
            mul_le_mul_of_nonneg_left h1 hpos.le
        _ = colMarg p b * q a (g b) / colMarg q (g b) - p a b := by
            field_simp
  -- the reference weights have the same total mass as `p`
  have hmass : ∑ a, ∑ b, (colMarg p b * q a (g b) / colMarg q (g b) - p a b) = 0 := by
    rw [sum_comm]
    have h1 : ∀ b, ∑ a, (colMarg p b * q a (g b) / colMarg q (g b) - p a b) = 0 := by
      intro b
      rw [sum_sub_distrib]
      have h2 : ∑ a, colMarg p b * q a (g b) / colMarg q (g b)
          = colMarg p b * (∑ a, q a (g b)) / colMarg q (g b) := by
        rw [mul_sum, sum_div]
      rw [h2, show ∑ a, q a (g b) = colMarg q (g b) from rfl,
        mul_div_assoc, div_self (hCpos b).ne', mul_one]
      simp [colMarg]
    exact sum_eq_zero fun b _ => h1 b
  -- conclude, working with natural logarithms
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [hIq]
  unfold mutualInfo
  simp only [Real.logb, mul_div_assoc']
  simp only [← sum_div]
  apply div_le_div_of_nonneg_right _ hlog2.le
  have h3 : ∑ a, ∑ b, p a b * Real.log (q a (g b) / (rowMarg p a * colMarg q (g b)))
      - ∑ a, ∑ b, p a b * Real.log (p a b / (rowMarg p a * colMarg p b)) ≤ 0 := by
    rw [← sum_sub_distrib, ← hmass]
    refine sum_le_sum fun a _ => ?_
    rw [← sum_sub_distrib]
    refine sum_le_sum fun b _ => ?_
    rw [← mul_sub]
    exact hterm a b
  linarith
