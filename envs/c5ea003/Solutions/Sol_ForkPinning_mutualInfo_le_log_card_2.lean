-- Prove2me | solution 2 for ForkPinning.mutualInfo_le_log_card
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T08:11:43.22398+00:00
-- url     : https://prove2.me/submissions/f9d1f8ff-95c6-4283-a55f-0ea7b13e9e60

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
open ForkPinning Finset Real in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] {κ β : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype β] [DecidableEq β] (X : Ω → κ) (Y : Ω → β) : mutualInfo X Y ≤ Real.log (Fintype.card κ) := by
  have hcard : (0 : ℝ) < Fintype.card Ω := by
    have := Fintype.card_pos (α := Ω)
    exact_mod_cast this
  have hjfib : ∀ (k : κ) (b : β),
      fiber (joint X Y) (k, b) = (fiber X k).filter (fun ω => Y ω = b) := by
    intro k b
    unfold fiber joint
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro ω _
    simp [Prod.ext_iff]
  have hjfib2 : ∀ (k : κ) (b : β),
      fiber (joint X Y) (k, b) = (fiber Y b).filter (fun ω => X ω = k) := by
    intro k b
    unfold fiber joint
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro ω _
    simp [Prod.ext_iff]
    tauto
  have hcm1 : ∀ k : κ, ∑ b : β, (fiber (joint X Y) (k, b)).card = (fiber X k).card := by
    intro k
    have h := Finset.card_eq_sum_card_fiberwise
      (f := Y) (s := fiber X k) (t := (Finset.univ : Finset β)) (fun x _ => Finset.mem_univ (Y x))
    rw [h]
    exact Finset.sum_congr rfl (fun b _ => by rw [hjfib k b])
  have hcm2 : ∀ b : β, ∑ k : κ, (fiber (joint X Y) (k, b)).card = (fiber Y b).card := by
    intro b
    have h := Finset.card_eq_sum_card_fiberwise
      (f := X) (s := fiber Y b) (t := (Finset.univ : Finset κ)) (fun x _ => Finset.mem_univ (X x))
    rw [h]
    exact Finset.sum_congr rfl (fun k _ => by rw [hjfib2 k b])
  have hmarg1 : ∀ k : κ, ∑ b : β, prb (joint X Y) (k, b) = prb X k := by
    intro k
    unfold prb
    rw [← Finset.sum_div]
    have hc : ∑ b : β, ((fiber (joint X Y) (k, b)).card : ℝ) = ((fiber X k).card : ℝ) := by
      have h := hcm1 k
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h
    rw [hc]
  have hmarg2 : ∀ b : β, ∑ k : κ, prb (joint X Y) (k, b) = prb Y b := by
    intro b
    unfold prb
    rw [← Finset.sum_div]
    have hc : ∑ k : κ, ((fiber (joint X Y) (k, b)).card : ℝ) = ((fiber Y b).card : ℝ) := by
      have h := hcm2 b
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h
    rw [hc]
  have hnnX : ∀ k : κ, 0 ≤ prb X k := by
    intro k
    unfold prb
    positivity
  have hnnY : ∀ b : β, 0 ≤ prb Y b := by
    intro b
    unfold prb
    positivity
  have hnnJ : ∀ p : κ × β, 0 ≤ prb (joint X Y) p := by
    intro p
    unfold prb
    positivity
  have hsumX : ∑ k : κ, prb X k = 1 := by
    unfold prb
    rw [← Finset.sum_div]
    have hc : ∑ k : κ, ((fiber X k).card : ℝ) = (Fintype.card Ω : ℝ) := by
      have h := Finset.card_eq_sum_card_fiberwise
        (f := X) (s := (Finset.univ : Finset Ω)) (t := (Finset.univ : Finset κ))
        (fun x _ => Finset.mem_univ (X x))
      rw [Finset.card_univ] at h
      have h2 : ∑ k : κ, (fiber X k).card = Fintype.card Ω := by
        unfold fiber
        exact h.symm
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h2
    rw [hc]
    field_simp
  have hsumY : ∑ b : β, prb Y b = 1 := by
    unfold prb
    rw [← Finset.sum_div]
    have hc : ∑ b : β, ((fiber Y b).card : ℝ) = (Fintype.card Ω : ℝ) := by
      have h := Finset.card_eq_sum_card_fiberwise
        (f := Y) (s := (Finset.univ : Finset Ω)) (t := (Finset.univ : Finset β))
        (fun x _ => Finset.mem_univ (Y x))
      rw [Finset.card_univ] at h
      have h2 : ∑ b : β, (fiber Y b).card = Fintype.card Ω := by
        unfold fiber
        exact h.symm
      exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h2
    rw [hc]
    field_simp
  have hle1 : ∀ (k : κ) (b : β), prb (joint X Y) (k, b) ≤ prb X k := by
    intro k b
    rw [← hmarg1 k]
    exact Finset.single_le_sum (fun b' _ => hnnJ (k, b')) (Finset.mem_univ b)
  have hle2 : ∀ (k : κ) (b : β), prb (joint X Y) (k, b) ≤ prb Y b := by
    intro k b
    rw [← hmarg2 b]
    exact Finset.single_le_sum (fun k' _ => hnnJ (k', b)) (Finset.mem_univ k)
  -- the mutual information as a KL divergence against the product
  have hident : mutualInfo X Y
      = ∑ p : κ × β, prb (joint X Y) p
          * Real.log (prb (joint X Y) p / (prb X p.1 * prb Y p.2)) := by
    have hHX : H X = ∑ k : κ, ∑ b : β, -(prb (joint X Y) (k, b) * Real.log (prb X k)) := by
      unfold H
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have e : ∑ b : β, -(prb (joint X Y) (k, b) * Real.log (prb X k))
          = -((∑ b : β, prb (joint X Y) (k, b)) * Real.log (prb X k)) := by
        rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      rw [e, hmarg1 k]
      unfold Real.negMulLog
      ring
    have hHY : H Y = ∑ k : κ, ∑ b : β, -(prb (joint X Y) (k, b) * Real.log (prb Y b)) := by
      unfold H
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      have e : ∑ k : κ, -(prb (joint X Y) (k, b) * Real.log (prb Y b))
          = -((∑ k : κ, prb (joint X Y) (k, b)) * Real.log (prb Y b)) := by
        rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      rw [e, hmarg2 b]
      unfold Real.negMulLog
      ring
    have hHJ : H (joint X Y)
        = ∑ k : κ, ∑ b : β, -(prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b))) := by
      unfold H
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun b _ => by
        unfold Real.negMulLog
        ring))
    unfold mutualInfo
    rw [hHX, hHY, hHJ, Fintype.sum_prod_type]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rcases eq_or_lt_of_le (hnnJ (k, b)) with h0 | h0
    · rw [← h0]
      simp
    · have hx : 0 < prb X k := lt_of_lt_of_le h0 (hle1 k b)
      have hy : 0 < prb Y b := lt_of_lt_of_le h0 (hle2 k b)
      rw [Real.log_div (ne_of_gt h0) (by positivity), Real.log_mul (ne_of_gt hx) (ne_of_gt hy)]
      ring
  have hHY : H Y = ∑ k : κ, ∑ b : β, -(prb (joint X Y) (k, b) * Real.log (prb Y b)) := by
    unfold H
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    have e : ∑ k : κ, -(prb (joint X Y) (k, b) * Real.log (prb Y b))
        = -((∑ k : κ, prb (joint X Y) (k, b)) * Real.log (prb Y b)) := by
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [e, hmarg2 b]
    unfold Real.negMulLog
    ring
  have hHJ : H (joint X Y)
      = ∑ k : κ, ∑ b : β, -(prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b))) := by
    unfold H
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun b _ => by
      unfold Real.negMulLog
      ring))
  have hmonoY : H Y ≤ H (joint X Y) := by
    rw [hHY, hHJ]
    refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun b _ => ?_))
    rcases eq_or_lt_of_le (hnnJ (k, b)) with h0 | h0
    · rw [← h0]
      simp
    · have hlog : Real.log (prb (joint X Y) (k, b)) ≤ Real.log (prb Y b) :=
        Real.log_le_log h0 (hle2 k b)
      have := mul_le_mul_of_nonneg_left hlog (le_of_lt h0)
      linarith
  -- the marginal entropy is at most log of the alphabet size
  have hne : Nonempty κ := ⟨X (Classical.arbitrary Ω)⟩
  have hn : (0 : ℝ) < (Fintype.card κ : ℝ) := by
    have := Fintype.card_pos (α := κ)
    exact_mod_cast this
  have hmul_log : ∀ t : ℝ, 0 ≤ t → t - 1 ≤ t * Real.log t := by
    intro t ht
    rcases eq_or_lt_of_le ht with h0 | h0
    · rw [← h0]
      simp
    · have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / t by positivity)
      rw [Real.log_div one_ne_zero (ne_of_gt h0), Real.log_one] at h1
      have h2 : 1 - 1 / t ≤ Real.log t := by linarith
      calc t - 1 = t * (1 - 1 / t) := by field_simp
        _ ≤ t * Real.log t := mul_le_mul_of_nonneg_left h2 ht
  have htangent : ∀ p : ℝ, 0 ≤ p →
      Real.negMulLog p ≤ p * Real.log (Fintype.card κ) - p + 1 / (Fintype.card κ : ℝ) := by
    intro p hp
    rcases eq_or_lt_of_le hp with hp0 | hp0
    · rw [← hp0]
      simp [Real.negMulLog]
    · have ht := hmul_log (p * (Fintype.card κ : ℝ)) (by positivity)
      rw [Real.log_mul (ne_of_gt hp0) (ne_of_gt hn)] at ht
      unfold Real.negMulLog
      have hfinal : 0 ≤ p * Real.log (Fintype.card κ) - p + 1 / (Fintype.card κ : ℝ)
          - (-p * Real.log p) := by
        have key : p * Real.log (Fintype.card κ) - p + 1 / (Fintype.card κ : ℝ)
            - (-p * Real.log p)
            = (p * (Fintype.card κ : ℝ) * (Real.log p + Real.log (Fintype.card κ : ℝ))
                - (p * (Fintype.card κ : ℝ) - 1)) / (Fintype.card κ : ℝ) := by
          field_simp
          ring
        rw [key]
        apply div_nonneg _ (le_of_lt hn)
        linarith [ht]
      linarith [hfinal]
  have hHXle : H X ≤ Real.log (Fintype.card κ) := by
    calc H X = ∑ k : κ, Real.negMulLog (prb X k) := rfl
      _ ≤ ∑ k : κ, (prb X k * Real.log (Fintype.card κ) - prb X k
            + 1 / (Fintype.card κ : ℝ)) :=
          Finset.sum_le_sum (fun k _ => htangent (prb X k) (hnnX k))
      _ = Real.log (Fintype.card κ) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumX,
            Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp
          ring
  have hgoal : mutualInfo X Y = H X + H Y - H (joint X Y) := rfl
  rw [hgoal]
  linarith [hmonoY, hHXle]
