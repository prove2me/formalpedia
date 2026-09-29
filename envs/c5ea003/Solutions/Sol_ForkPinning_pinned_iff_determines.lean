-- Prove2me | solution 1 for ForkPinning.pinned_iff_determines
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T08:24:08.496988+00:00
-- url     : https://prove2.me/submissions/badec082-0de2-4d27-bd64-f7f911bb0b75

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
open ForkPinning Finset Real in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] {κ β : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype β] [DecidableEq β] (X : Ω → κ) (Y : Ω → β) : mutualInfo X Y = H Y ↔ Determines X Y := by
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
  have hposJ : ∀ ω : Ω, 0 < prb (joint X Y) (X ω, Y ω) := by
    intro ω
    unfold prb
    have hmem : ω ∈ fiber (joint X Y) (X ω, Y ω) := by
      unfold fiber joint
      simp
    have hc : 0 < ((fiber (joint X Y) (X ω, Y ω)).card : ℝ) := by
      have := Finset.card_pos.mpr ⟨ω, hmem⟩
      exact_mod_cast this
    exact div_pos hc hcard
  have hposX : ∀ ω : Ω, 0 < prb X (X ω) := by
    intro ω
    unfold prb
    have hmem : ω ∈ fiber X (X ω) := by
      unfold fiber
      simp
    have hc : 0 < ((fiber X (X ω)).card : ℝ) := by
      have := Finset.card_pos.mpr ⟨ω, hmem⟩
      exact_mod_cast this
    exact div_pos hc hcard
  have htermle : ∀ (k : κ) (b : β),
      -(prb (joint X Y) (k, b) * Real.log (prb X k))
        ≤ -(prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b))) := by
    intro k b
    rcases eq_or_lt_of_le (hnnJ (k, b)) with h0 | h0
    · rw [← h0]
      simp
    · have hlog : Real.log (prb (joint X Y) (k, b)) ≤ Real.log (prb X k) :=
        Real.log_le_log h0 (hle1 k b)
      have := mul_le_mul_of_nonneg_left hlog (le_of_lt h0)
      linarith
  have hgoal : mutualInfo X Y = H X + H Y - H (joint X Y) := rfl
  constructor
  · intro heq
    have hHeq : H X = H (joint X Y) := by
      rw [hgoal] at heq
      linarith
    rw [hHX, hHJ] at hHeq
    have houter := (Finset.sum_eq_sum_iff_of_le (fun k _ =>
      Finset.sum_le_sum (fun b _ => htermle k b))).mp hHeq
    intro ω ω' hX
    by_contra hne
    have hinner := (Finset.sum_eq_sum_iff_of_le (fun b _ => htermle (X ω) b)).mp
      (houter (X ω) (Finset.mem_univ (X ω)))
    have hkey : ∀ b : β, 0 < prb (joint X Y) (X ω, b) →
        prb X (X ω) = prb (joint X Y) (X ω, b) := by
      intro b hb
      have h1 := hinner b (Finset.mem_univ b)
      have hne0 : prb (joint X Y) (X ω, b) ≠ 0 := ne_of_gt hb
      have h3 : prb (joint X Y) (X ω, b) * Real.log (prb X (X ω))
          = prb (joint X Y) (X ω, b) * Real.log (prb (joint X Y) (X ω, b)) := by linarith [h1]
      have h2 : Real.log (prb X (X ω)) = Real.log (prb (joint X Y) (X ω, b)) :=
        mul_left_cancel₀ hne0 h3
      have hx : 0 < prb X (X ω) := lt_of_lt_of_le hb (hle1 (X ω) b)
      exact (Real.log_injOn_pos (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hb) h2)
    have hb1 := hkey (Y ω) (hposJ ω)
    have hb2 : prb X (X ω) = prb (joint X Y) (X ω, Y ω') := by
      refine hkey (Y ω') ?_
      have h := hposJ ω'
      rw [← hX] at h
      exact h
    have hpair : prb (joint X Y) (X ω, Y ω) + prb (joint X Y) (X ω, Y ω')
        ≤ ∑ b : β, prb (joint X Y) (X ω, b) := by
      have e : ∑ b ∈ ({Y ω, Y ω'} : Finset β), prb (joint X Y) (X ω, b)
          = prb (joint X Y) (X ω, Y ω) + prb (joint X Y) (X ω, Y ω') := Finset.sum_pair hne
      rw [← e]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun b _ _ => hnnJ (X ω, b))
    rw [hmarg1 (X ω)] at hpair
    have hx : 0 < prb X (X ω) := hposX ω
    linarith
  · intro hdet
    have hHeq : H X = H (joint X Y) := by
      rw [hHX, hHJ]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun b _ => ?_))
      rcases eq_or_lt_of_le (hnnJ (k, b)) with h0 | h0
      · rw [← h0]
        simp
      · have hsubset : fiber X k ⊆ fiber (joint X Y) (k, b) := by
          intro ω hω
          unfold fiber at hω ⊢
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
          have hex : ∃ ω₀, X ω₀ = k ∧ Y ω₀ = b := by
            by_contra hcon
            have hzero : fiber (joint X Y) (k, b) = ∅ := by
              unfold fiber joint
              rw [Finset.filter_eq_empty_iff]
              intro ω₀ _
              intro hEq
              exact hcon ⟨ω₀, (Prod.ext_iff.mp hEq).1, (Prod.ext_iff.mp hEq).2⟩
            have : prb (joint X Y) (k, b) = 0 := by
              unfold prb
              rw [hzero]
              simp
            linarith
          obtain ⟨ω₀, hω₀X, hω₀Y⟩ := hex
          refine Prod.ext ?_ ?_
          · exact hω
          · rw [← hω₀Y]
            exact hdet ω ω₀ (by rw [hω, hω₀X])
        have hsubset2 : fiber (joint X Y) (k, b) ⊆ fiber X k := by
          intro ω hω
          unfold fiber joint at hω
          unfold fiber
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
          exact (Prod.ext_iff.mp hω).1
        have hcards : prb X k = prb (joint X Y) (k, b) := by
          unfold prb
          rw [Finset.Subset.antisymm hsubset hsubset2]
        rw [hcards]
    rw [hgoal]
    linarith
