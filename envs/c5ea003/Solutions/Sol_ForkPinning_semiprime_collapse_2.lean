-- Prove2me | solution 2 for ForkPinning.semiprime_collapse
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T22:58:57.600769+00:00
-- url     : https://prove2.me/submissions/49ae7309-c0aa-49cf-981d-68c4ef749b6a

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningGalois
import Definitions.Def_Probability_ForkPinningSemiprime
open ForkPinning Finset Real in
theorem solution :
    12 * mutualInfo cubicClassOfN splitOR < mutualInfo (id : ZMod 3 → ZMod 3) forkC3 := by
  have hcard3 : Fintype.card (ZMod 3) = 3 := by simp
  have hcard9 : Fintype.card (ZMod 3 × ZMod 3) = 9 := by simp
  -- ===== side A: the semiprime class against "some factor splits" =====
  have cA : ∀ g : ZMod 3, (fiber cubicClassOfN g).card = 3 := by decide
  have cYt : (fiber splitOR true).card = 5 := by decide
  have cYf : (fiber splitOR false).card = 4 := by decide
  have hpair : ∀ g : ZMod 3,
      ((fiber (joint cubicClassOfN splitOR) (g, true)).card = 1
        ∧ (fiber (joint cubicClassOfN splitOR) (g, false)).card = 2)
      ∨ ((fiber (joint cubicClassOfN splitOR) (g, true)).card = 2
        ∧ (fiber (joint cubicClassOfN splitOR) (g, false)).card = 1) := by decide
  have hHXa : H cubicClassOfN = 3 * negMulLog (1 / 3 : ℝ) := by
    have e : ∀ g : ZMod 3, prb cubicClassOfN g = 1 / 3 := by
      intro g
      simp only [prb, cA g, hcard9]
      norm_num
    simp only [H, e]
    rw [Finset.sum_const, Finset.card_univ, hcard3, nsmul_eq_mul]
    norm_num
  have hHYa : H splitOR = negMulLog (5 / 9 : ℝ) + negMulLog (4 / 9 : ℝ) := by
    have e1 : prb splitOR true = 5 / 9 := by simp only [prb, cYt, hcard9]; norm_num
    have e2 : prb splitOR false = 4 / 9 := by simp only [prb, cYf, hcard9]; norm_num
    simp only [H]
    rw [Fintype.sum_bool, e1, e2]
  have hHJa : H (joint cubicClassOfN splitOR)
      = 3 * (negMulLog (1 / 9 : ℝ) + negMulLog (2 / 9 : ℝ)) := by
    have hinner : ∀ g : ZMod 3,
        (∑ b : Bool, negMulLog (prb (joint cubicClassOfN splitOR) (g, b)))
          = negMulLog (1 / 9 : ℝ) + negMulLog (2 / 9 : ℝ) := by
      intro g
      rw [Fintype.sum_bool]
      rcases hpair g with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have q1 : prb (joint cubicClassOfN splitOR) (g, true) = 1 / 9 := by
          simp only [prb, h1, hcard9]; norm_num
        have q2 : prb (joint cubicClassOfN splitOR) (g, false) = 2 / 9 := by
          simp only [prb, h2, hcard9]; norm_num
        rw [q1, q2]
      · have q1 : prb (joint cubicClassOfN splitOR) (g, true) = 2 / 9 := by
          simp only [prb, h1, hcard9]; norm_num
        have q2 : prb (joint cubicClassOfN splitOR) (g, false) = 1 / 9 := by
          simp only [prb, h2, hcard9]; norm_num
        rw [q1, q2]
        ring
    simp only [H]
    rw [Fintype.sum_prod_type]
    simp only [hinner]
    rw [Finset.sum_const, Finset.card_univ, hcard3, nsmul_eq_mul]
    norm_num
  have hA : mutualInfo cubicClassOfN splitOR
      = 3 * negMulLog (1 / 3 : ℝ) + (negMulLog (5 / 9 : ℝ) + negMulLog (4 / 9 : ℝ))
        - 3 * (negMulLog (1 / 9 : ℝ) + negMulLog (2 / 9 : ℝ)) := by
    simp only [mutualInfo, hHXa, hHYa, hHJa]
  -- ===== side B: the cyclic cubic fork against the class itself =====
  have hfX : ∀ k : ZMod 3, fiber (id : ZMod 3 → ZMod 3) k = {k} := by
    intro k
    ext x
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, id_eq, Finset.mem_singleton]
  have hHXb : H (id : ZMod 3 → ZMod 3) = 3 * negMulLog (1 / 3 : ℝ) := by
    have e : ∀ k : ZMod 3, prb (id : ZMod 3 → ZMod 3) k = 1 / 3 := by
      intro k
      simp only [prb, hfX k, Finset.card_singleton, hcard3]
      norm_num
    simp only [H, e]
    rw [Finset.sum_const, Finset.card_univ, hcard3, nsmul_eq_mul]
    norm_num
  have hHYb : H forkC3 = negMulLog (1 / 3 : ℝ) + negMulLog (2 / 3 : ℝ) := by
    have c1 : (fiber forkC3 true).card = 1 := by decide
    have c2 : (fiber forkC3 false).card = 2 := by decide
    have e1 : prb forkC3 true = 1 / 3 := by simp only [prb, c1, hcard3]; norm_num
    have e2 : prb forkC3 false = 2 / 3 := by simp only [prb, c2, hcard3]; norm_num
    simp only [H]
    rw [Fintype.sum_bool, e1, e2]
  have hfJ : ∀ (k : ZMod 3) (b : Bool),
      (fiber (joint (id : ZMod 3 → ZMod 3) forkC3) (k, b)).card
        = if forkC3 k = b then 1 else 0 := by
    intro k b
    by_cases hb : forkC3 k = b
    · have he : fiber (joint (id : ZMod 3 → ZMod 3) forkC3) (k, b) = {k} := by
        ext x
        simp only [fiber, joint, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq,
          id_eq, Finset.mem_singleton]
        constructor
        · intro hx; exact hx.1
        · intro hx; subst hx; exact ⟨rfl, hb⟩
      rw [he, Finset.card_singleton, if_pos hb]
    · have he : fiber (joint (id : ZMod 3 → ZMod 3) forkC3) (k, b) = ∅ := by
        ext x
        simp only [fiber, joint, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq,
          id_eq, Finset.notMem_empty, iff_false, not_and]
        intro hx
        subst hx
        exact hb
      rw [he, Finset.card_empty, if_neg hb]
  have hHJb : H (joint (id : ZMod 3 → ZMod 3) forkC3) = 3 * negMulLog (1 / 3 : ℝ) := by
    have hpJ : ∀ (k : ZMod 3) (b : Bool),
        prb (joint (id : ZMod 3 → ZMod 3) forkC3) (k, b)
          = (if forkC3 k = b then (1 : ℝ) else 0) / 3 := by
      intro k b
      simp only [prb, hfJ k b, hcard3]
      by_cases hb : forkC3 k = b
      · simp [hb]
      · simp [hb]
    have hinner : ∀ k : ZMod 3,
        (∑ b : Bool, negMulLog (prb (joint (id : ZMod 3 → ZMod 3) forkC3) (k, b)))
          = negMulLog (1 / 3 : ℝ) := by
      intro k
      rw [Fintype.sum_bool, hpJ k true, hpJ k false]
      by_cases hk : forkC3 k = true
      · simp [hk]
      · rw [Bool.not_eq_true] at hk
        simp [hk]
    simp only [H]
    rw [Fintype.sum_prod_type]
    simp only [hinner]
    rw [Finset.sum_const, Finset.card_univ, hcard3, nsmul_eq_mul]
    norm_num
  have hB : mutualInfo (id : ZMod 3 → ZMod 3) forkC3
      = negMulLog (1 / 3 : ℝ) + negMulLog (2 / 3 : ℝ) := by
    simp only [mutualInfo, hHXb, hHYb, hHJb]
    ring
  -- ===== the numerical heart: 3^33 < 5^20 · 2^6 =====
  have hkey : 33 * Real.log 3 < 20 * Real.log 5 + 6 * Real.log 2 := by
    have h1 : Real.log ((3 : ℝ) ^ 33) < Real.log ((5 : ℝ) ^ 20 * (2 : ℝ) ^ 6) := by
      apply Real.log_lt_log (by positivity)
      norm_num
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_pow] at h1
    push_cast at h1
    linarith
  have hL9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hl13 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by rw [one_div, Real.log_inv]
  have hl19 : Real.log (1 / 9 : ℝ) = -(2 * Real.log 3) := by
    rw [one_div, Real.log_inv, hL9]
  have hl29 : Real.log (2 / 9 : ℝ) = Real.log 2 - 2 * Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), hL9]
  have hl59 : Real.log (5 / 9 : ℝ) = Real.log 5 - 2 * Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), hL9]
  have hl49 : Real.log (4 / 9 : ℝ) = 2 * Real.log 2 - 2 * Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), hL9, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    push_cast
    ring
  have hl23 : Real.log (2 / 3 : ℝ) = Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  rw [hA, hB]
  simp only [Real.negMulLog_def]
  rw [hl13, hl59, hl49, hl19, hl29, hl23]
  linarith [hkey]
