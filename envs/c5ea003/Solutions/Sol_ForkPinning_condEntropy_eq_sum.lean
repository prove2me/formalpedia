-- Prove2me | solution 1 for ForkPinning.condEntropy_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T08:17:36.660954+00:00
-- url     : https://prove2.me/submissions/3aec9049-ffb3-431d-9030-4de522d3e697

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
open ForkPinning Finset Real in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] {κ β : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype β] [DecidableEq β] (X : Ω → κ) (Y : Ω → β) : condEntropy X Y = ∑ k : κ, prb X k * condEntropyAt X Y k := by
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
  have hHX : H X = ∑ k : κ, ∑ b : β, -(prb (joint X Y) (k, b) * Real.log (prb X k)) := by
    unfold H
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have e : ∑ b : β, -(prb (joint X Y) (k, b) * Real.log (prb X k))
        = -((∑ b : β, prb (joint X Y) (k, b)) * Real.log (prb X k)) := by
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [e, hmarg1 k]
    unfold Real.negMulLog
    ring
  have hHJ : H (joint X Y)
      = ∑ k : κ, ∑ b : β, -(prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b))) := by
    unfold H
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun b _ => by
      unfold Real.negMulLog
      ring))
  have hterm : ∀ k : κ, prb X k * condEntropyAt X Y k
      = ∑ b : β, (-(prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b)))
          - -(prb (joint X Y) (k, b) * Real.log (prb X k))) := by
    intro k
    unfold condEntropyAt condPrb
    rcases eq_or_lt_of_le (hnnX k) with h0 | h0
    · have hz : ∀ b : β, prb (joint X Y) (k, b) = 0 := by
        intro b
        have h1 := hle1 k b
        have h2 := hnnJ (k, b)
        linarith [h0]
      rw [← h0, zero_mul]
      refine (Finset.sum_eq_zero (fun b _ => ?_)).symm
      rw [hz b]
      simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rcases eq_or_lt_of_le (hnnJ (k, b)) with hj | hj
      · rw [← hj]
        simp [Real.negMulLog]
      · unfold Real.negMulLog
        rw [Real.log_div (ne_of_gt hj) (ne_of_gt h0)]
        field_simp
        ring
  have hsum : ∑ k : κ, prb X k * condEntropyAt X Y k = H (joint X Y) - H X := by
    rw [Finset.sum_congr rfl (fun k _ => hterm k), hHJ, hHX, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_sub_distrib]
  have hgoal : condEntropy X Y = H (joint X Y) - H X := rfl
  rw [hgoal, hsum]
