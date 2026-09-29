-- Prove2me | solution 2 for ForkPinning.capacity_attained_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T23:35:27.815907+00:00
-- url     : https://prove2.me/submissions/d13a3eba-a8f0-44e4-aef0-f3a386b87891

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningGalois
open ForkPinning Finset Real in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : Ω → κ) (Y : Ω → Bool) :
    mutualInfo X Y = Real.log 2 ↔ Determines X Y ∧ prb Y true = 1 / 2 := by
  -- (1) pinning is determination
  have hpin : mutualInfo X Y = H Y ↔ Determines X Y := by
    have hcard : (0 : ℝ) < Fintype.card Ω := by
      have := Fintype.card_pos (α := Ω)
      exact_mod_cast this
    have hjfib : ∀ (k : κ) (b : Bool),
        fiber (joint X Y) (k, b) = (fiber X k).filter (fun ω => Y ω = b) := by
      intro k b
      unfold fiber joint
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro ω _
      simp [Prod.ext_iff]
    have hjfib2 : ∀ (k : κ) (b : Bool),
        fiber (joint X Y) (k, b) = (fiber Y b).filter (fun ω => X ω = k) := by
      intro k b
      unfold fiber joint
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro ω _
      simp [Prod.ext_iff]
      tauto
    have hcm1 : ∀ k : κ, ∑ b : Bool, (fiber (joint X Y) (k, b)).card = (fiber X k).card := by
      intro k
      have h := Finset.card_eq_sum_card_fiberwise
        (f := Y) (s := fiber X k) (t := (Finset.univ : Finset Bool)) (fun x _ => Finset.mem_univ (Y x))
      rw [h]
      exact Finset.sum_congr rfl (fun b _ => by rw [hjfib k b])
    have hcm2 : ∀ b : Bool, ∑ k : κ, (fiber (joint X Y) (k, b)).card = (fiber Y b).card := by
      intro b
      have h := Finset.card_eq_sum_card_fiberwise
        (f := X) (s := fiber Y b) (t := (Finset.univ : Finset κ)) (fun x _ => Finset.mem_univ (X x))
      rw [h]
      exact Finset.sum_congr rfl (fun k _ => by rw [hjfib2 k b])
    have hmarg1 : ∀ k : κ, ∑ b : Bool, prb (joint X Y) (k, b) = prb X k := by
      intro k
      unfold prb
      rw [← Finset.sum_div]
      have hc : ∑ b : Bool, ((fiber (joint X Y) (k, b)).card : ℝ) = ((fiber X k).card : ℝ) := by
        have h := hcm1 k
        exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h
      rw [hc]
    have hmarg2 : ∀ b : Bool, ∑ k : κ, prb (joint X Y) (k, b) = prb Y b := by
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
    have hnnY : ∀ b : Bool, 0 ≤ prb Y b := by
      intro b
      unfold prb
      positivity
    have hnnJ : ∀ p : κ × Bool, 0 ≤ prb (joint X Y) p := by
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
    have hsumY : ∑ b : Bool, prb Y b = 1 := by
      unfold prb
      rw [← Finset.sum_div]
      have hc : ∑ b : Bool, ((fiber Y b).card : ℝ) = (Fintype.card Ω : ℝ) := by
        have h := Finset.card_eq_sum_card_fiberwise
          (f := Y) (s := (Finset.univ : Finset Ω)) (t := (Finset.univ : Finset Bool))
          (fun x _ => Finset.mem_univ (Y x))
        rw [Finset.card_univ] at h
        have h2 : ∑ b : Bool, (fiber Y b).card = Fintype.card Ω := by
          unfold fiber
          exact h.symm
        exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h2
      rw [hc]
      field_simp
    have hle1 : ∀ (k : κ) (b : Bool), prb (joint X Y) (k, b) ≤ prb X k := by
      intro k b
      rw [← hmarg1 k]
      exact Finset.single_le_sum (fun b' _ => hnnJ (k, b')) (Finset.mem_univ b)
    have hle2 : ∀ (k : κ) (b : Bool), prb (joint X Y) (k, b) ≤ prb Y b := by
      intro k b
      rw [← hmarg2 b]
      exact Finset.single_le_sum (fun k' _ => hnnJ (k', b)) (Finset.mem_univ k)
    -- the mutual information as a KL divergence against the product
    have hident : mutualInfo X Y
        = ∑ p : κ × Bool, prb (joint X Y) p
            * Real.log (prb (joint X Y) p / (prb X p.1 * prb Y p.2)) := by
      have hHX : H X = ∑ k : κ, ∑ b : Bool, -(prb (joint X Y) (k, b) * Real.log (prb X k)) := by
        unfold H
        refine Finset.sum_congr rfl (fun k _ => ?_)
        have e : ∑ b : Bool, -(prb (joint X Y) (k, b) * Real.log (prb X k))
            = -((∑ b : Bool, prb (joint X Y) (k, b)) * Real.log (prb X k)) := by
          rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
        rw [e, hmarg1 k]
        unfold Real.negMulLog
        ring
      have hHY : H Y = ∑ k : κ, ∑ b : Bool, -(prb (joint X Y) (k, b) * Real.log (prb Y b)) := by
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
          = ∑ k : κ, ∑ b : Bool, -(prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b))) := by
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
    have hHX : H X = ∑ k : κ, ∑ b : Bool, -(prb (joint X Y) (k, b) * Real.log (prb X k)) := by
      unfold H
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have e : ∑ b : Bool, -(prb (joint X Y) (k, b) * Real.log (prb X k))
          = -((∑ b : Bool, prb (joint X Y) (k, b)) * Real.log (prb X k)) := by
        rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      rw [e, hmarg1 k]
      unfold Real.negMulLog
      ring
    have hHJ : H (joint X Y)
        = ∑ k : κ, ∑ b : Bool, -(prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b))) := by
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
    have htermle : ∀ (k : κ) (b : Bool),
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
      have hkey : ∀ b : Bool, 0 < prb (joint X Y) (X ω, b) →
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
          ≤ ∑ b : Bool, prb (joint X Y) (X ω, b) := by
        have e : ∑ b ∈ ({Y ω, Y ω'} : Finset Bool), prb (joint X Y) (X ω, b)
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
  -- (2) a Bool statistic has entropy log 2 exactly when it is balanced
  have hbool : H Y = Real.log 2 ↔ prb Y true = 1 / 2 := by
    have hcard : (0 : ℝ) < Fintype.card Ω := by
      have := Fintype.card_pos (α := Ω)
      exact_mod_cast this
    have hnn : ∀ b : Bool, 0 ≤ prb Y b := by
      intro b
      unfold prb
      positivity
    have hsum : prb Y true + prb Y false = 1 := by
      have hfib : ∑ b : Bool, (fiber Y b).card = Fintype.card Ω := by
        have h := Finset.card_eq_sum_card_fiberwise
          (f := Y) (s := (Finset.univ : Finset Ω)) (t := (Finset.univ : Finset Bool))
          (fun x _ => Finset.mem_univ (Y x))
        rw [Finset.card_univ] at h
        unfold fiber
        exact h.symm
      have h1 : ∑ b : Bool, prb Y b = 1 := by
        unfold prb
        rw [← Finset.sum_div]
        have hc : ∑ b : Bool, ((fiber Y b).card : ℝ) = (Fintype.card Ω : ℝ) := by
          exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) hfib
        rw [hc]
        field_simp
      rw [Fintype.sum_bool] at h1
      exact h1
    have hHY : H Y = Real.negMulLog (prb Y true) + Real.negMulLog (prb Y false) := by
      unfold H
      rw [Fintype.sum_bool]
    have hfalse : prb Y false = 1 - prb Y true := by linarith
    have hhalf : Real.negMulLog (1 / 2 : ℝ) = Real.log 2 / 2 := by
      unfold Real.negMulLog
      rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
      ring
    constructor
    · intro heq
      by_contra hne
      have hxy : prb Y true ≠ prb Y false := by
        rw [hfalse]
        intro h
        exact hne (by linarith)
      have hsc := Real.strictConcaveOn_negMulLog.2 (Set.mem_Ici.mpr (hnn true))
        (Set.mem_Ici.mpr (hnn false)) hxy (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
        (by norm_num)
      rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at hsc
      have hmid : (1/2 : ℝ) * prb Y true + (1/2 : ℝ) * prb Y false = 1/2 := by linarith
      rw [hmid, hhalf] at hsc
      rw [hHY] at heq
      linarith
    · intro hp
      rw [hHY, hp, hfalse, hp, show (1 : ℝ) - 1/2 = 1/2 by norm_num, hhalf]
      ring
  -- (3) mutual information never exceeds the fork's entropy
  have hle : mutualInfo X Y ≤ H Y := by
    have hcard : (0 : ℝ) < Fintype.card Ω := by
      have := Fintype.card_pos (α := Ω)
      exact_mod_cast this
    have hjfib : ∀ (k : κ) (b : Bool),
        fiber (joint X Y) (k, b) = (fiber X k).filter (fun ω => Y ω = b) := by
      intro k b
      unfold fiber joint
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro ω _
      simp [Prod.ext_iff]
    have hjfib2 : ∀ (k : κ) (b : Bool),
        fiber (joint X Y) (k, b) = (fiber Y b).filter (fun ω => X ω = k) := by
      intro k b
      unfold fiber joint
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro ω _
      simp [Prod.ext_iff]
      tauto
    have hcm1 : ∀ k : κ, ∑ b : Bool, (fiber (joint X Y) (k, b)).card = (fiber X k).card := by
      intro k
      have h := Finset.card_eq_sum_card_fiberwise
        (f := Y) (s := fiber X k) (t := (Finset.univ : Finset Bool)) (fun x _ => Finset.mem_univ (Y x))
      rw [h]
      exact Finset.sum_congr rfl (fun b _ => by rw [hjfib k b])
    have hcm2 : ∀ b : Bool, ∑ k : κ, (fiber (joint X Y) (k, b)).card = (fiber Y b).card := by
      intro b
      have h := Finset.card_eq_sum_card_fiberwise
        (f := X) (s := fiber Y b) (t := (Finset.univ : Finset κ)) (fun x _ => Finset.mem_univ (X x))
      rw [h]
      exact Finset.sum_congr rfl (fun k _ => by rw [hjfib2 k b])
    have hmarg1 : ∀ k : κ, ∑ b : Bool, prb (joint X Y) (k, b) = prb X k := by
      intro k
      unfold prb
      rw [← Finset.sum_div]
      have hc : ∑ b : Bool, ((fiber (joint X Y) (k, b)).card : ℝ) = ((fiber X k).card : ℝ) := by
        have h := hcm1 k
        exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h
      rw [hc]
    have hmarg2 : ∀ b : Bool, ∑ k : κ, prb (joint X Y) (k, b) = prb Y b := by
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
    have hnnY : ∀ b : Bool, 0 ≤ prb Y b := by
      intro b
      unfold prb
      positivity
    have hnnJ : ∀ p : κ × Bool, 0 ≤ prb (joint X Y) p := by
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
    have hsumY : ∑ b : Bool, prb Y b = 1 := by
      unfold prb
      rw [← Finset.sum_div]
      have hc : ∑ b : Bool, ((fiber Y b).card : ℝ) = (Fintype.card Ω : ℝ) := by
        have h := Finset.card_eq_sum_card_fiberwise
          (f := Y) (s := (Finset.univ : Finset Ω)) (t := (Finset.univ : Finset Bool))
          (fun x _ => Finset.mem_univ (Y x))
        rw [Finset.card_univ] at h
        have h2 : ∑ b : Bool, (fiber Y b).card = Fintype.card Ω := by
          unfold fiber
          exact h.symm
        exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h2
      rw [hc]
      field_simp
    have hle1 : ∀ (k : κ) (b : Bool), prb (joint X Y) (k, b) ≤ prb X k := by
      intro k b
      rw [← hmarg1 k]
      exact Finset.single_le_sum (fun b' _ => hnnJ (k, b')) (Finset.mem_univ b)
    have hle2 : ∀ (k : κ) (b : Bool), prb (joint X Y) (k, b) ≤ prb Y b := by
      intro k b
      rw [← hmarg2 b]
      exact Finset.single_le_sum (fun k' _ => hnnJ (k', b)) (Finset.mem_univ k)
    -- the mutual information as a KL divergence against the product
    have hident : mutualInfo X Y
        = ∑ p : κ × Bool, prb (joint X Y) p
            * Real.log (prb (joint X Y) p / (prb X p.1 * prb Y p.2)) := by
      have hHX : H X = ∑ k : κ, ∑ b : Bool, -(prb (joint X Y) (k, b) * Real.log (prb X k)) := by
        unfold H
        refine Finset.sum_congr rfl (fun k _ => ?_)
        have e : ∑ b : Bool, -(prb (joint X Y) (k, b) * Real.log (prb X k))
            = -((∑ b : Bool, prb (joint X Y) (k, b)) * Real.log (prb X k)) := by
          rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
        rw [e, hmarg1 k]
        unfold Real.negMulLog
        ring
      have hHY : H Y = ∑ k : κ, ∑ b : Bool, -(prb (joint X Y) (k, b) * Real.log (prb Y b)) := by
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
          = ∑ k : κ, ∑ b : Bool, -(prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b))) := by
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
    -- the joint entropy dominates the marginal entropy, termwise
    have hHX : H X = ∑ k : κ, ∑ b : Bool, -(prb (joint X Y) (k, b) * Real.log (prb X k)) := by
      unfold H
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have e : ∑ b : Bool, -(prb (joint X Y) (k, b) * Real.log (prb X k))
          = -((∑ b : Bool, prb (joint X Y) (k, b)) * Real.log (prb X k)) := by
        rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      rw [e, hmarg1 k]
      unfold Real.negMulLog
      ring
    have hHJ : H (joint X Y)
        = ∑ k : κ, ∑ b : Bool, -(prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b))) := by
      unfold H
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun b _ => by
        unfold Real.negMulLog
        ring))
    have hmono : H X ≤ H (joint X Y) := by
      rw [hHX, hHJ]
      refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun b _ => ?_))
      rcases eq_or_lt_of_le (hnnJ (k, b)) with h0 | h0
      · rw [← h0]
        simp
      · have hx : 0 < prb X k := lt_of_lt_of_le h0 (hle1 k b)
        have hlog : Real.log (prb (joint X Y) (k, b)) ≤ Real.log (prb X k) :=
          Real.log_le_log h0 (hle1 k b)
        have := mul_le_mul_of_nonneg_left hlog (le_of_lt h0)
        linarith
    have hgoal : mutualInfo X Y = H X + H Y - H (joint X Y) := rfl
    rw [hgoal]
    linarith [hmono]
  -- (4) a Bool statistic has entropy at most log 2
  have hcb : ∀ Z : Ω → Bool, H Z ≤ Real.log (Fintype.card Bool) := by
    intro Z
    have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hnnZ : ∀ k : Bool, 0 ≤ prb Z k := by
      intro k
      unfold prb
      positivity
    have hsumZ : ∑ k : Bool, prb Z k = 1 := by
      simp only [prb, fiber]
      rw [← Finset.sum_div, div_eq_one_iff_eq hΩ, ← Nat.cast_sum]
      congr 1
      rw [← Finset.card_univ (α := Ω)]
      exact (Finset.card_eq_sum_card_fiberwise
        (fun ω _ => Finset.mem_coe.mpr (Finset.mem_univ _))).symm
    have hne : Nonempty Bool := ⟨Z (Classical.arbitrary Ω)⟩
    have hn : (0 : ℝ) < (Fintype.card Bool : ℝ) := by
      have := Fintype.card_pos (α := Bool)
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
        Real.negMulLog p ≤ p * Real.log (Fintype.card Bool) - p + 1 / (Fintype.card Bool : ℝ) := by
      intro p hp
      rcases eq_or_lt_of_le hp with hp0 | hp0
      · rw [← hp0]
        simp [Real.negMulLog]
      · have ht := hmul_log (p * (Fintype.card Bool : ℝ)) (by positivity)
        rw [Real.log_mul (ne_of_gt hp0) (ne_of_gt hn)] at ht
        unfold Real.negMulLog
        have hfinal : 0 ≤ p * Real.log (Fintype.card Bool) - p + 1 / (Fintype.card Bool : ℝ)
            - (-p * Real.log p) := by
          have key : p * Real.log (Fintype.card Bool) - p + 1 / (Fintype.card Bool : ℝ)
              - (-p * Real.log p)
              = (p * (Fintype.card Bool : ℝ) * (Real.log p + Real.log (Fintype.card Bool : ℝ))
                  - (p * (Fintype.card Bool : ℝ) - 1)) / (Fintype.card Bool : ℝ) := by
            field_simp
            ring
          rw [key]
          apply div_nonneg _ (le_of_lt hn)
          linarith [ht]
        linarith [hfinal]
    calc H Z = ∑ k : Bool, Real.negMulLog (prb Z k) := rfl
      _ ≤ ∑ k : Bool, (prb Z k * Real.log (Fintype.card Bool) - prb Z k
            + 1 / (Fintype.card Bool : ℝ)) :=
          Finset.sum_le_sum (fun k _ => htangent (prb Z k) (hnnZ k))
      _ = Real.log (Fintype.card Bool) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumZ,
            Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp
          ring
  have hlog : H Y ≤ Real.log 2 := by
    have h := hcb Y
    simpa using h
  constructor
  · intro h
    have hge : Real.log 2 ≤ H Y := by rw [← h]; exact hle
    have hHY : H Y = Real.log 2 := le_antisymm hlog hge
    exact ⟨hpin.mp (by rw [h, hHY]), hbool.mp hHY⟩
  · rintro ⟨hdet, hbal⟩
    rw [hpin.mpr hdet, hbool.mpr hbal]
