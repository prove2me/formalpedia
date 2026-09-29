-- Prove2me | solution 1 for ForkPinning.mutualInfo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T08:05:16.642792+00:00
-- url     : https://prove2.me/submissions/5e275904-d118-4c63-8a64-481339d51a28

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
open ForkPinning Finset Real in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] {κ β : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype β] [DecidableEq β] (X : Ω → κ) (Y : Ω → β) : 0 ≤ mutualInfo X Y := by
  classical
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
  -- Gibbs inequality on the support
  have hkey : ∀ a b : ℝ, 0 ≤ a → 0 < b → 0 ≤ a * Real.log (a / b) - (a - b) := by
    intro a b ha hb
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · rw [← ha0]
      simp
      linarith
    · have hlog : 1 - b / a ≤ Real.log (a / b) := by
        have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < b / a by positivity)
        rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha0)] at h1
        rw [Real.log_div (ne_of_gt ha0) (ne_of_gt hb)]
        linarith
      have h2 := mul_le_mul_of_nonneg_left hlog (le_of_lt ha0)
      have he : a * (1 - b / a) = a - b := by field_simp
      rw [he] at h2
      linarith
  set S : Finset (κ × β) := Finset.univ.filter (fun p => 0 < prb (joint X Y) p) with hSdef
  have hcompl : ∀ p ∈ (Finset.univ : Finset (κ × β)) \ S, prb (joint X Y) p = 0 := by
    intro p hp
    rw [Finset.mem_sdiff, hSdef, Finset.mem_filter] at hp
    rcases eq_or_lt_of_le (hnnJ p) with h0 | h0
    · exact h0.symm
    · exact absurd ⟨Finset.mem_univ p, h0⟩ hp.2
  have hsumS : ∑ p ∈ S, prb (joint X Y) p = 1 := by
    have hall : ∑ p : κ × β, prb (joint X Y) p = 1 := by
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_congr rfl (fun k _ => hmarg1 k)]
      exact hsumX
    rw [← hall, ← Finset.sum_subset (Finset.subset_univ S) (fun p hp hpS => hcompl p
      (Finset.mem_sdiff.mpr ⟨hp, hpS⟩))]
  have hprodle : ∑ p ∈ S, prb X p.1 * prb Y p.2 ≤ 1 := by
    have hall : ∑ p : κ × β, prb X p.1 * prb Y p.2 = 1 := by
      rw [Fintype.sum_prod_type]
      have e : ∀ k : κ, ∑ b : β, prb X k * prb Y b = prb X k := by
        intro k
        rw [← Finset.mul_sum, hsumY, mul_one]
      rw [Finset.sum_congr rfl (fun k _ => e k)]
      exact hsumX
    rw [← hall]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) ?_
    intro p _ _
    exact mul_nonneg (hnnX p.1) (hnnY p.2)
  have hlow : 0 ≤ ∑ p ∈ S, prb (joint X Y) p
      * Real.log (prb (joint X Y) p / (prb X p.1 * prb Y p.2)) := by
    have h1 : 0 ≤ ∑ p ∈ S, (prb (joint X Y) p
        * Real.log (prb (joint X Y) p / (prb X p.1 * prb Y p.2))
        - (prb (joint X Y) p - prb X p.1 * prb Y p.2)) := by
      refine Finset.sum_nonneg (fun p hp => ?_)
      rw [hSdef, Finset.mem_filter] at hp
      have hx : 0 < prb X p.1 := lt_of_lt_of_le hp.2 (by
        have := hle1 p.1 p.2
        simpa using this)
      have hy : 0 < prb Y p.2 := lt_of_lt_of_le hp.2 (by
        have := hle2 p.1 p.2
        simpa using this)
      exact hkey _ _ (hnnJ p) (by positivity)
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsumS] at h1
    linarith
  rw [hident, ← Finset.sum_subset (Finset.subset_univ S) (fun p hp hpS => by
    rw [hcompl p (Finset.mem_sdiff.mpr ⟨hp, hpS⟩)]
    simp)]
  exact hlow
