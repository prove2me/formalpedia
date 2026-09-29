-- Prove2me | solution 1 for ForkPinning.mutualInfo_comp_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T01:54:17.776459+00:00
-- url     : https://prove2.me/submissions/f79c1936-e131-479f-8715-960fa09b4448

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningDataProcessing
import Definitions.Def_Probability_ForkPinningGalois

/- Equality in the data-processing inequality holds exactly when the coarse statistic
`g ∘ X` is a sufficient statistic for `Y`.  The proof sums the elementary Gibbs term
`r log r − r log s − r + s` (with `s = q·p/P` the coarse prediction of the fine cell) over
all cells: the sum is exactly `I(X;Y) − I(gX;Y)`, and each term is non-negative and vanishes
precisely when `r = s`. -/
set_option maxHeartbeats 4000000 in
open ForkPinning Finset Real in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] {κ κ' β : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] [Fintype β] [DecidableEq β]
    (g : κ → κ') (X : Ω → κ) (Y : Ω → β) :
    mutualInfo (fun ω => g (X ω)) Y = mutualInfo X Y
      ↔ ∀ k b, prb (joint X Y) (k, b)
          = prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k
              / prb (fun ω => g (X ω)) (g k) := by
  classical
  ---------------------------------------------------------------- counting helpers
  have hΩpos : (0:ℝ) < (Fintype.card Ω : ℝ) := by
    have h := Fintype.card_pos (α := Ω); positivity
  have hΩne : (Fintype.card Ω : ℝ) ≠ 0 := ne_of_gt hΩpos
  have cardnn : ∀ s : Finset Ω, (0:ℝ) ≤ (s.card : ℝ) / (Fintype.card Ω : ℝ) := by
    intro s; positivity
  have cardpos : ∀ s : Finset Ω, s.Nonempty → (0:ℝ) < (s.card : ℝ) / (Fintype.card Ω : ℝ) := by
    intro s hs
    have h1 : 0 < s.card := Finset.card_pos.mpr hs
    positivity
  ---------------------------------------------------------------- total mass
  have sumX : ∑ c : κ, prb X c = 1 := by
    unfold prb
    rw [← Finset.sum_div, ← Nat.cast_sum]
    have h : ∑ c : κ, (fiber X c).card = Fintype.card Ω := by
      simp only [fiber]
      rw [← Finset.card_univ (α := Ω)]
      exact (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (X x))).symm
    rw [h]; field_simp
  have sumG : ∑ c : κ', prb (fun ω => g (X ω)) c = 1 := by
    unfold prb
    rw [← Finset.sum_div, ← Nat.cast_sum]
    have h : ∑ c : κ', (fiber (fun ω => g (X ω)) c).card = Fintype.card Ω := by
      simp only [fiber]
      rw [← Finset.card_univ (α := Ω)]
      exact (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (g (X x)))).symm
    rw [h]; field_simp
  ---------------------------------------------------------------- marginals
  have margX : ∀ c : κ, ∑ b : β, prb (joint X Y) (c, b) = prb X c := by
    intro c
    unfold prb
    rw [← Finset.sum_div, ← Nat.cast_sum]
    congr 2
    have hfib : ∀ b : β, fiber (joint X Y) (c, b) = (fiber X c).filter (fun ω => Y ω = b) := by
      intro b; ext ω; simp [fiber, joint, Prod.ext_iff]
    simp only [hfib]
    exact (Finset.card_eq_sum_card_fiberwise
      (f := Y) (s := fiber X c) (t := (univ : Finset β)) (fun x _ => Finset.mem_univ _)).symm
  have margG : ∀ c : κ', ∑ b : β, prb (joint (fun ω => g (X ω)) Y) (c, b)
      = prb (fun ω => g (X ω)) c := by
    intro c
    unfold prb
    rw [← Finset.sum_div, ← Nat.cast_sum]
    congr 2
    have hfib : ∀ b : β, fiber (joint (fun ω => g (X ω)) Y) (c, b)
        = (fiber (fun ω => g (X ω)) c).filter (fun ω => Y ω = b) := by
      intro b; ext ω; simp [fiber, joint, Prod.ext_iff]
    simp only [hfib]
    exact (Finset.card_eq_sum_card_fiberwise
      (f := Y) (s := fiber (fun ω => g (X ω)) c) (t := (univ : Finset β))
      (fun x _ => Finset.mem_univ _)).symm
  ---------------------------------------------------------------- fibrewise grouping along `g`
  have grpX : ∀ k' : κ',
      ∑ k ∈ univ.filter (fun k => g k = k'), prb X k = prb (fun ω => g (X ω)) k' := by
    intro k'
    unfold prb
    rw [← Finset.sum_div, ← Nat.cast_sum]
    congr 2
    have hmap : ∀ ω ∈ fiber (fun ω => g (X ω)) k', X ω ∈ univ.filter (fun k => g k = k') := by
      intro ω hw
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact hw
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    congr 1
    ext ω
    have h3 : X ω = k → g (X ω) = k' := fun h => by rw [h, hk]
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have grpJ : ∀ (k' : κ') (b : β),
      ∑ k ∈ univ.filter (fun k => g k = k'), prb (joint X Y) (k, b)
        = prb (joint (fun ω => g (X ω)) Y) (k', b) := by
    intro k' b
    unfold prb
    rw [← Finset.sum_div, ← Nat.cast_sum]
    congr 2
    have hmap : ∀ ω ∈ fiber (joint (fun ω => g (X ω)) Y) (k', b),
        X ω ∈ univ.filter (fun k => g k = k') := by
      intro ω hw
      simp only [fiber, joint, Prod.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact hw.1
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    congr 1
    ext ω
    have h3 : X ω = k → g (X ω) = k' := fun h => by rw [h, hk]
    simp only [fiber, joint, Prod.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  ---------------------------------------------------------------- reindexing along `g`
  have reidx : ∀ (w : κ → β → ℝ) (W : κ' → β → ℝ),
      (∀ (k' : κ') (b : β), ∑ k ∈ univ.filter (fun k => g k = k'), w k b = W k' b) →
      ∀ F : κ' → β → ℝ,
        ∑ k : κ, ∑ b : β, w k b * F (g k) b = ∑ k' : κ', ∑ b : β, W k' b * F k' b := by
    intro w W hgrp F
    rw [← Finset.sum_fiberwise (univ : Finset κ) g (fun k => ∑ b : β, w k b * F (g k) b)]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hgrp k' b, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [hk]
  ---------------------------------------------------------------- the six sum identities
  have hA : ∑ k : κ, ∑ b : β, prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b)) = - H (joint X Y) := by
    unfold H
    rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Real.negMulLog]; ring
  have hB : ∑ k : κ, ∑ b : β, prb (joint X Y) (k, b) * Real.log (prb (joint (fun ω => g (X ω)) Y) (g k, b))
      = - H (joint (fun ω => g (X ω)) Y) := by
    rw [reidx (fun k b => prb (joint X Y) (k, b))
      (fun k' b => prb (joint (fun ω => g (X ω)) Y) (k', b)) grpJ
      (fun k' b => Real.log (prb (joint (fun ω => g (X ω)) Y) (k', b)))]
    unfold H
    rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Real.negMulLog]; ring
  have hC : ∑ k : κ, ∑ b : β, prb (joint X Y) (k, b) * Real.log (prb X k) = - H X := by
    unfold H
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul, margX k]
    simp only [Real.negMulLog]; ring
  have hD : ∑ k : κ, ∑ b : β, prb (joint X Y) (k, b) * Real.log (prb (fun ω => g (X ω)) (g k))
      = - H (fun ω => g (X ω)) := by
    rw [reidx (fun k b => prb (joint X Y) (k, b))
      (fun k' b => prb (joint (fun ω => g (X ω)) Y) (k', b)) grpJ
      (fun k' _ => Real.log (prb (fun ω => g (X ω)) k'))]
    unfold H
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [← Finset.sum_mul, margG k']
    simp only [Real.negMulLog]; ring
  have hR1 : ∑ k : κ, ∑ b : β, prb (joint X Y) (k, b) = 1 := by
    simp only [margX]
    exact sumX
  have hE1 : ∑ k : κ, ∑ b : β, prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k) = 1 := by
    have hrw : ∀ (k : κ) (b : β), prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k)
          = prb X k *
            ((fun k' b => prb (joint (fun ω => g (X ω)) Y) (k', b)
              / prb (fun ω => g (X ω)) k') (g k) b) := by
      intro k b; simp only; ring
    simp only [hrw]
    rw [reidx (fun k _ => prb X k) (fun k' _ => prb (fun ω => g (X ω)) k')
      (fun k' _ => grpX k')
      (fun k' b => prb (joint (fun ω => g (X ω)) Y) (k', b) / prb (fun ω => g (X ω)) k')]
    have hin : ∀ k' : κ', ∑ b : β,
        prb (fun ω => g (X ω)) k' *
          (prb (joint (fun ω => g (X ω)) Y) (k', b) / prb (fun ω => g (X ω)) k')
        = prb (fun ω => g (X ω)) k' := by
      intro k'
      have h0 : 0 ≤ prb (fun ω => g (X ω)) k' := by unfold prb; exact cardnn _
      rcases h0.eq_or_lt with h | h
      · simp [← h]
      · rw [← Finset.mul_sum, ← Finset.sum_div, margG k']
        field_simp
    simp only [hin]
    exact sumG
  ---------------------------------------------------------------- the master identity
  have hsum : ∑ k : κ, ∑ b : β, (prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b)) - prb (joint X Y) (k, b) * Real.log (prb (joint (fun ω => g (X ω)) Y) (g k, b)) - prb (joint X Y) (k, b) * Real.log (prb X k)
          + prb (joint X Y) (k, b) * Real.log (prb (fun ω => g (X ω)) (g k)) - prb (joint X Y) (k, b) + prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k))
      = mutualInfo X Y - mutualInfo (fun ω => g (X ω)) Y := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hA, hB, hC, hD, hR1, hE1]
    unfold mutualInfo
    ring
  ---------------------------------------------------------------- the pointwise Gibbs term
  have hkey : ∀ (k : κ) (b : β), 0 ≤ (prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b)) - prb (joint X Y) (k, b) * Real.log (prb (joint (fun ω => g (X ω)) Y) (g k, b)) - prb (joint X Y) (k, b) * Real.log (prb X k)
          + prb (joint X Y) (k, b) * Real.log (prb (fun ω => g (X ω)) (g k)) - prb (joint X Y) (k, b) + prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k)) ∧ ((prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b)) - prb (joint X Y) (k, b) * Real.log (prb (joint (fun ω => g (X ω)) Y) (g k, b)) - prb (joint X Y) (k, b) * Real.log (prb X k)
          + prb (joint X Y) (k, b) * Real.log (prb (fun ω => g (X ω)) (g k)) - prb (joint X Y) (k, b) + prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k)) = 0 ↔ prb (joint X Y) (k, b) = prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k)) := by
    intro k b
    have hrn : 0 ≤ prb (joint X Y) (k, b) := by unfold prb; exact cardnn _
    have hq0 : 0 ≤ prb (joint (fun ω => g (X ω)) Y) (g k, b) := by unfold prb; exact cardnn _
    have hp0 : 0 ≤ prb X k := by unfold prb; exact cardnn _
    have hP0 : 0 ≤ prb (fun ω => g (X ω)) (g k) := by unfold prb; exact cardnn _
    have hsn : 0 ≤ prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k) := div_nonneg (mul_nonneg hq0 hp0) hP0
    rcases hrn.eq_or_lt with h0 | hpos
    · -- an empty fine cell: the Gibbs term collapses to the coarse prediction
      have hU : (prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b)) - prb (joint X Y) (k, b) * Real.log (prb (joint (fun ω => g (X ω)) Y) (g k, b)) - prb (joint X Y) (k, b) * Real.log (prb X k)
          + prb (joint X Y) (k, b) * Real.log (prb (fun ω => g (X ω)) (g k)) - prb (joint X Y) (k, b) + prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k)) = prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k) := by rw [← h0]; ring
      refine ⟨by rw [hU]; exact hsn, ?_⟩
      rw [hU, ← h0]
      exact eq_comm
    · -- a populated fine cell forces all three marginals to be positive
      obtain ⟨ω, hω⟩ : ∃ ω : Ω, X ω = k ∧ Y ω = b := by
        have hcard : 0 < (fiber (joint X Y) (k, b)).card := by
          rcases Nat.eq_zero_or_pos (fiber (joint X Y) (k, b)).card with hz | hz
          · unfold prb at hpos
            rw [hz] at hpos
            simp at hpos
          · exact hz
        obtain ⟨ω, hωmem⟩ := Finset.card_pos.mp hcard
        simp only [fiber, joint, Finset.mem_filter, Finset.mem_univ, true_and,
          Prod.ext_iff] at hωmem
        exact ⟨ω, hωmem.1, hωmem.2⟩
      have hpk : 0 < prb X k := by
        unfold prb; exact cardpos _ ⟨ω, by simp [fiber, hω.1]⟩
      have hpp : 0 < prb (fun ω => g (X ω)) (g k) := by
        unfold prb; exact cardpos _ ⟨ω, by simp [fiber, hω.1]⟩
      have hqq : 0 < prb (joint (fun ω => g (X ω)) Y) (g k, b) := by
        unfold prb; exact cardpos _ ⟨ω, by simp [fiber, joint, hω.1, hω.2]⟩
      have hsp : 0 < prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k) := div_pos (mul_pos hqq hpk) hpp
      have hlog : Real.log (prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k)) = Real.log (prb (joint (fun ω => g (X ω)) Y) (g k, b)) + Real.log (prb X k) - Real.log (prb (fun ω => g (X ω)) (g k)) := by
        rw [Real.log_div (ne_of_gt (mul_pos hqq hpk)) (ne_of_gt hpp),
          Real.log_mul (ne_of_gt hqq) (ne_of_gt hpk)]
      have hUeq : (prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b)) - prb (joint X Y) (k, b) * Real.log (prb (joint (fun ω => g (X ω)) Y) (g k, b)) - prb (joint X Y) (k, b) * Real.log (prb X k)
          + prb (joint X Y) (k, b) * Real.log (prb (fun ω => g (X ω)) (g k)) - prb (joint X Y) (k, b) + prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k)) = prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b)) - prb (joint X Y) (k, b) * Real.log (prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k)) - prb (joint X Y) (k, b) + prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k) := by
        rw [hlog]; ring
      have hdp : (0:ℝ) < prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k) / prb (joint X Y) (k, b) := div_pos hsp hpos
      have hfs : prb (joint X Y) (k, b) * (prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k) / prb (joint X Y) (k, b) - 1) = prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k) - prb (joint X Y) (k, b) := by field_simp
      refine ⟨?_, ?_⟩
      · rw [hUeq]
        have key : Real.log (prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k) / prb (joint X Y) (k, b)) ≤ prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k) / prb (joint X Y) (k, b) - 1 := Real.log_le_sub_one_of_pos hdp
        rw [Real.log_div (ne_of_gt hsp) (ne_of_gt hpos)] at key
        have h2 := mul_le_mul_of_nonneg_left key (le_of_lt hpos)
        rw [hfs] at h2
        nlinarith [h2]
      · rw [hUeq]
        refine ⟨?_, ?_⟩
        · intro hzero
          by_contra hne
          have hne1 : prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k) / prb (joint X Y) (k, b) ≠ 1 := by
            intro hh
            rw [div_eq_one_iff_eq (ne_of_gt hpos)] at hh
            exact hne hh.symm
          have key : Real.log (prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k) / prb (joint X Y) (k, b)) < prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k) / prb (joint X Y) (k, b) - 1 :=
            Real.log_lt_sub_one_of_pos hdp hne1
          rw [Real.log_div (ne_of_gt hsp) (ne_of_gt hpos)] at key
          have h2 := mul_lt_mul_of_pos_left key hpos
          rw [hfs] at h2
          nlinarith [h2]
        · intro heq; rw [← heq]; ring
  ---------------------------------------------------------------- assembling the equivalence
  constructor
  · intro heq k b
    have hz : ∑ k : κ, ∑ b : β, (prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b)) - prb (joint X Y) (k, b) * Real.log (prb (joint (fun ω => g (X ω)) Y) (g k, b)) - prb (joint X Y) (k, b) * Real.log (prb X k)
          + prb (joint X Y) (k, b) * Real.log (prb (fun ω => g (X ω)) (g k)) - prb (joint X Y) (k, b) + prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k)) = 0 := by rw [hsum, heq]; ring
    have houter : ∀ k : κ, ∑ b : β, (prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b)) - prb (joint X Y) (k, b) * Real.log (prb (joint (fun ω => g (X ω)) Y) (g k, b)) - prb (joint X Y) (k, b) * Real.log (prb X k)
          + prb (joint X Y) (k, b) * Real.log (prb (fun ω => g (X ω)) (g k)) - prb (joint X Y) (k, b) + prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k)) = 0 := by
      have hnn : ∀ k ∈ (univ : Finset κ), 0 ≤ ∑ b : β, (prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b)) - prb (joint X Y) (k, b) * Real.log (prb (joint (fun ω => g (X ω)) Y) (g k, b)) - prb (joint X Y) (k, b) * Real.log (prb X k)
          + prb (joint X Y) (k, b) * Real.log (prb (fun ω => g (X ω)) (g k)) - prb (joint X Y) (k, b) + prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k)) :=
        fun k _ => Finset.sum_nonneg fun b _ => (hkey k b).1
      intro k
      exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz k (Finset.mem_univ k)
    have hinner : (prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b)) - prb (joint X Y) (k, b) * Real.log (prb (joint (fun ω => g (X ω)) Y) (g k, b)) - prb (joint X Y) (k, b) * Real.log (prb X k)
          + prb (joint X Y) (k, b) * Real.log (prb (fun ω => g (X ω)) (g k)) - prb (joint X Y) (k, b) + prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun b _ => (hkey k b).1)).mp (houter k) b (Finset.mem_univ b)
    exact (hkey k b).2.mp hinner
  · intro hcond
    have hall : ∀ (k : κ) (b : β), (prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b)) - prb (joint X Y) (k, b) * Real.log (prb (joint (fun ω => g (X ω)) Y) (g k, b)) - prb (joint X Y) (k, b) * Real.log (prb X k)
          + prb (joint X Y) (k, b) * Real.log (prb (fun ω => g (X ω)) (g k)) - prb (joint X Y) (k, b) + prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k)) = 0 := fun k b => (hkey k b).2.mpr (hcond k b)
    have hz : ∑ k : κ, ∑ b : β, (prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b)) - prb (joint X Y) (k, b) * Real.log (prb (joint (fun ω => g (X ω)) Y) (g k, b)) - prb (joint X Y) (k, b) * Real.log (prb X k)
          + prb (joint X Y) (k, b) * Real.log (prb (fun ω => g (X ω)) (g k)) - prb (joint X Y) (k, b) + prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k / prb (fun ω => g (X ω)) (g k)) = 0 := by
      simp only [hall]
      simp
    rw [hsum] at hz
    linarith
