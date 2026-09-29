-- Prove2me | solution 1 for ForkPinning.sign_capacity_attained_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T23:40:38.231337+00:00
-- url     : https://prove2.me/submissions/d0e6942f-2de3-4973-bd02-77a53058964b

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningGalois
open ForkPinning Finset Real in
theorem solution {n : ℕ} (hn : 2 ≤ n) (Y : Equiv.Perm (Fin n) → Bool) :
    mutualInfo (signBool : Equiv.Perm (Fin n) → Bool) Y = Real.log 2
      ↔ (Y = (signBool : Equiv.Perm (Fin n) → Bool) ∨
          Y = fun σ : Equiv.Perm (Fin n) => !(signBool σ)) := by
  -- (A) the capacity criterion, re-proved inline
  have hcap : ∀ W Z : Equiv.Perm (Fin n) → Bool,
      mutualInfo W Z = Real.log 2 ↔ Determines W Z ∧ prb Z true = 1 / 2 := by
    intro W Z
    -- (1) pinning is determination
    have hpin : mutualInfo W Z = H Z ↔ Determines W Z := by
      have hcard : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by
        have := Fintype.card_pos (α := (Equiv.Perm (Fin n)))
        exact_mod_cast this
      have hjfib : ∀ (k : Bool) (b : Bool),
          fiber (joint W Z) (k, b) = (fiber W k).filter (fun ω => Z ω = b) := by
        intro k b
        unfold fiber joint
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro ω _
        simp [Prod.ext_iff]
      have hjfib2 : ∀ (k : Bool) (b : Bool),
          fiber (joint W Z) (k, b) = (fiber Z b).filter (fun ω => W ω = k) := by
        intro k b
        unfold fiber joint
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro ω _
        simp [Prod.ext_iff]
        tauto
      have hcm1 : ∀ k : Bool, ∑ b : Bool, (fiber (joint W Z) (k, b)).card = (fiber W k).card := by
        intro k
        have h := Finset.card_eq_sum_card_fiberwise
          (f := Z) (s := fiber W k) (t := (Finset.univ : Finset Bool)) (fun x _ => Finset.mem_univ (Z x))
        rw [h]
        exact Finset.sum_congr rfl (fun b _ => by rw [hjfib k b])
      have hcm2 : ∀ b : Bool, ∑ k : Bool, (fiber (joint W Z) (k, b)).card = (fiber Z b).card := by
        intro b
        have h := Finset.card_eq_sum_card_fiberwise
          (f := W) (s := fiber Z b) (t := (Finset.univ : Finset Bool)) (fun x _ => Finset.mem_univ (W x))
        rw [h]
        exact Finset.sum_congr rfl (fun k _ => by rw [hjfib2 k b])
      have hmarg1 : ∀ k : Bool, ∑ b : Bool, prb (joint W Z) (k, b) = prb W k := by
        intro k
        unfold prb
        rw [← Finset.sum_div]
        have hc : ∑ b : Bool, ((fiber (joint W Z) (k, b)).card : ℝ) = ((fiber W k).card : ℝ) := by
          have h := hcm1 k
          exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h
        rw [hc]
      have hmarg2 : ∀ b : Bool, ∑ k : Bool, prb (joint W Z) (k, b) = prb Z b := by
        intro b
        unfold prb
        rw [← Finset.sum_div]
        have hc : ∑ k : Bool, ((fiber (joint W Z) (k, b)).card : ℝ) = ((fiber Z b).card : ℝ) := by
          have h := hcm2 b
          exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h
        rw [hc]
      have hnnW : ∀ k : Bool, 0 ≤ prb W k := by
        intro k
        unfold prb
        positivity
      have hnnZ : ∀ b : Bool, 0 ≤ prb Z b := by
        intro b
        unfold prb
        positivity
      have hnnJ : ∀ p : Bool × Bool, 0 ≤ prb (joint W Z) p := by
        intro p
        unfold prb
        positivity
      have hsumW : ∑ k : Bool, prb W k = 1 := by
        unfold prb
        rw [← Finset.sum_div]
        have hc : ∑ k : Bool, ((fiber W k).card : ℝ) = (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
          have h := Finset.card_eq_sum_card_fiberwise
            (f := W) (s := (Finset.univ : Finset (Equiv.Perm (Fin n)))) (t := (Finset.univ : Finset Bool))
            (fun x _ => Finset.mem_univ (W x))
          rw [Finset.card_univ] at h
          have h2 : ∑ k : Bool, (fiber W k).card = Fintype.card (Equiv.Perm (Fin n)) := by
            unfold fiber
            exact h.symm
          exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h2
        rw [hc]
        field_simp
      have hsumZ : ∑ b : Bool, prb Z b = 1 := by
        unfold prb
        rw [← Finset.sum_div]
        have hc : ∑ b : Bool, ((fiber Z b).card : ℝ) = (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
          have h := Finset.card_eq_sum_card_fiberwise
            (f := Z) (s := (Finset.univ : Finset (Equiv.Perm (Fin n)))) (t := (Finset.univ : Finset Bool))
            (fun x _ => Finset.mem_univ (Z x))
          rw [Finset.card_univ] at h
          have h2 : ∑ b : Bool, (fiber Z b).card = Fintype.card (Equiv.Perm (Fin n)) := by
            unfold fiber
            exact h.symm
          exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h2
        rw [hc]
        field_simp
      have hle1 : ∀ (k : Bool) (b : Bool), prb (joint W Z) (k, b) ≤ prb W k := by
        intro k b
        rw [← hmarg1 k]
        exact Finset.single_le_sum (fun b' _ => hnnJ (k, b')) (Finset.mem_univ b)
      have hle2 : ∀ (k : Bool) (b : Bool), prb (joint W Z) (k, b) ≤ prb Z b := by
        intro k b
        rw [← hmarg2 b]
        exact Finset.single_le_sum (fun k' _ => hnnJ (k', b)) (Finset.mem_univ k)
      -- the mutual information as a KL divergence against the product
      have hident : mutualInfo W Z
          = ∑ p : Bool × Bool, prb (joint W Z) p
              * Real.log (prb (joint W Z) p / (prb W p.1 * prb Z p.2)) := by
        have hHW : H W = ∑ k : Bool, ∑ b : Bool, -(prb (joint W Z) (k, b) * Real.log (prb W k)) := by
          unfold H
          refine Finset.sum_congr rfl (fun k _ => ?_)
          have e : ∑ b : Bool, -(prb (joint W Z) (k, b) * Real.log (prb W k))
              = -((∑ b : Bool, prb (joint W Z) (k, b)) * Real.log (prb W k)) := by
            rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
          rw [e, hmarg1 k]
          unfold Real.negMulLog
          ring
        have hHZ : H Z = ∑ k : Bool, ∑ b : Bool, -(prb (joint W Z) (k, b) * Real.log (prb Z b)) := by
          unfold H
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          have e : ∑ k : Bool, -(prb (joint W Z) (k, b) * Real.log (prb Z b))
              = -((∑ k : Bool, prb (joint W Z) (k, b)) * Real.log (prb Z b)) := by
            rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
          rw [e, hmarg2 b]
          unfold Real.negMulLog
          ring
        have hHJ : H (joint W Z)
            = ∑ k : Bool, ∑ b : Bool, -(prb (joint W Z) (k, b) * Real.log (prb (joint W Z) (k, b))) := by
          unfold H
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun b _ => by
            unfold Real.negMulLog
            ring))
        unfold mutualInfo
        rw [hHW, hHZ, hHJ, Fintype.sum_prod_type]
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rcases eq_or_lt_of_le (hnnJ (k, b)) with h0 | h0
        · rw [← h0]
          simp
        · have hx : 0 < prb W k := lt_of_lt_of_le h0 (hle1 k b)
          have hy : 0 < prb Z b := lt_of_lt_of_le h0 (hle2 k b)
          rw [Real.log_div (ne_of_gt h0) (by positivity), Real.log_mul (ne_of_gt hx) (ne_of_gt hy)]
          ring
      have hHW : H W = ∑ k : Bool, ∑ b : Bool, -(prb (joint W Z) (k, b) * Real.log (prb W k)) := by
        unfold H
        refine Finset.sum_congr rfl (fun k _ => ?_)
        have e : ∑ b : Bool, -(prb (joint W Z) (k, b) * Real.log (prb W k))
            = -((∑ b : Bool, prb (joint W Z) (k, b)) * Real.log (prb W k)) := by
          rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
        rw [e, hmarg1 k]
        unfold Real.negMulLog
        ring
      have hHJ : H (joint W Z)
          = ∑ k : Bool, ∑ b : Bool, -(prb (joint W Z) (k, b) * Real.log (prb (joint W Z) (k, b))) := by
        unfold H
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun b _ => by
          unfold Real.negMulLog
          ring))
      have hposJ : ∀ ω : (Equiv.Perm (Fin n)), 0 < prb (joint W Z) (W ω, Z ω) := by
        intro ω
        unfold prb
        have hmem : ω ∈ fiber (joint W Z) (W ω, Z ω) := by
          unfold fiber joint
          simp
        have hc : 0 < ((fiber (joint W Z) (W ω, Z ω)).card : ℝ) := by
          have := Finset.card_pos.mpr ⟨ω, hmem⟩
          exact_mod_cast this
        exact div_pos hc hcard
      have hposW : ∀ ω : (Equiv.Perm (Fin n)), 0 < prb W (W ω) := by
        intro ω
        unfold prb
        have hmem : ω ∈ fiber W (W ω) := by
          unfold fiber
          simp
        have hc : 0 < ((fiber W (W ω)).card : ℝ) := by
          have := Finset.card_pos.mpr ⟨ω, hmem⟩
          exact_mod_cast this
        exact div_pos hc hcard
      have htermle : ∀ (k : Bool) (b : Bool),
          -(prb (joint W Z) (k, b) * Real.log (prb W k))
            ≤ -(prb (joint W Z) (k, b) * Real.log (prb (joint W Z) (k, b))) := by
        intro k b
        rcases eq_or_lt_of_le (hnnJ (k, b)) with h0 | h0
        · rw [← h0]
          simp
        · have hlog : Real.log (prb (joint W Z) (k, b)) ≤ Real.log (prb W k) :=
            Real.log_le_log h0 (hle1 k b)
          have := mul_le_mul_of_nonneg_left hlog (le_of_lt h0)
          linarith
      have hgoal : mutualInfo W Z = H W + H Z - H (joint W Z) := rfl
      constructor
      · intro heq
        have hHeq : H W = H (joint W Z) := by
          rw [hgoal] at heq
          linarith
        rw [hHW, hHJ] at hHeq
        have houter := (Finset.sum_eq_sum_iff_of_le (fun k _ =>
          Finset.sum_le_sum (fun b _ => htermle k b))).mp hHeq
        intro ω ω' hW
        by_contra hne
        have hinner := (Finset.sum_eq_sum_iff_of_le (fun b _ => htermle (W ω) b)).mp
          (houter (W ω) (Finset.mem_univ (W ω)))
        have hkey : ∀ b : Bool, 0 < prb (joint W Z) (W ω, b) →
            prb W (W ω) = prb (joint W Z) (W ω, b) := by
          intro b hb
          have h1 := hinner b (Finset.mem_univ b)
          have hne0 : prb (joint W Z) (W ω, b) ≠ 0 := ne_of_gt hb
          have h3 : prb (joint W Z) (W ω, b) * Real.log (prb W (W ω))
              = prb (joint W Z) (W ω, b) * Real.log (prb (joint W Z) (W ω, b)) := by linarith [h1]
          have h2 : Real.log (prb W (W ω)) = Real.log (prb (joint W Z) (W ω, b)) :=
            mul_left_cancel₀ hne0 h3
          have hx : 0 < prb W (W ω) := lt_of_lt_of_le hb (hle1 (W ω) b)
          exact (Real.log_injOn_pos (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hb) h2)
        have hb1 := hkey (Z ω) (hposJ ω)
        have hb2 : prb W (W ω) = prb (joint W Z) (W ω, Z ω') := by
          refine hkey (Z ω') ?_
          have h := hposJ ω'
          rw [← hW] at h
          exact h
        have hpair : prb (joint W Z) (W ω, Z ω) + prb (joint W Z) (W ω, Z ω')
            ≤ ∑ b : Bool, prb (joint W Z) (W ω, b) := by
          have e : ∑ b ∈ ({Z ω, Z ω'} : Finset Bool), prb (joint W Z) (W ω, b)
              = prb (joint W Z) (W ω, Z ω) + prb (joint W Z) (W ω, Z ω') := Finset.sum_pair hne
          rw [← e]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun b _ _ => hnnJ (W ω, b))
        rw [hmarg1 (W ω)] at hpair
        have hx : 0 < prb W (W ω) := hposW ω
        linarith
      · intro hdet
        have hHeq : H W = H (joint W Z) := by
          rw [hHW, hHJ]
          refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun b _ => ?_))
          rcases eq_or_lt_of_le (hnnJ (k, b)) with h0 | h0
          · rw [← h0]
            simp
          · have hsubset : fiber W k ⊆ fiber (joint W Z) (k, b) := by
              intro ω hω
              unfold fiber at hω ⊢
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
              have hex : ∃ ω₀, W ω₀ = k ∧ Z ω₀ = b := by
                by_contra hcon
                have hzero : fiber (joint W Z) (k, b) = ∅ := by
                  unfold fiber joint
                  rw [Finset.filter_eq_empty_iff]
                  intro ω₀ _
                  intro hEq
                  exact hcon ⟨ω₀, (Prod.ext_iff.mp hEq).1, (Prod.ext_iff.mp hEq).2⟩
                have : prb (joint W Z) (k, b) = 0 := by
                  unfold prb
                  rw [hzero]
                  simp
                linarith
              obtain ⟨ω₀, hω₀W, hω₀Z⟩ := hex
              refine Prod.ext ?_ ?_
              · exact hω
              · rw [← hω₀Z]
                exact hdet ω ω₀ (by rw [hω, hω₀W])
            have hsubset2 : fiber (joint W Z) (k, b) ⊆ fiber W k := by
              intro ω hω
              unfold fiber joint at hω
              unfold fiber
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
              exact (Prod.ext_iff.mp hω).1
            have hcards : prb W k = prb (joint W Z) (k, b) := by
              unfold prb
              rw [Finset.Subset.antisymm hsubset hsubset2]
            rw [hcards]
        rw [hgoal]
        linarith
    -- (2) a Bool statistic has entropy log 2 exactly when it is balanced
    have hbool : H Z = Real.log 2 ↔ prb Z true = 1 / 2 := by
      have hcard : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by
        have := Fintype.card_pos (α := (Equiv.Perm (Fin n)))
        exact_mod_cast this
      have hnn : ∀ b : Bool, 0 ≤ prb Z b := by
        intro b
        unfold prb
        positivity
      have hsum : prb Z true + prb Z false = 1 := by
        have hfib : ∑ b : Bool, (fiber Z b).card = Fintype.card (Equiv.Perm (Fin n)) := by
          have h := Finset.card_eq_sum_card_fiberwise
            (f := Z) (s := (Finset.univ : Finset (Equiv.Perm (Fin n)))) (t := (Finset.univ : Finset Bool))
            (fun x _ => Finset.mem_univ (Z x))
          rw [Finset.card_univ] at h
          unfold fiber
          exact h.symm
        have h1 : ∑ b : Bool, prb Z b = 1 := by
          unfold prb
          rw [← Finset.sum_div]
          have hc : ∑ b : Bool, ((fiber Z b).card : ℝ) = (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
            exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) hfib
          rw [hc]
          field_simp
        rw [Fintype.sum_bool] at h1
        exact h1
      have hHZ : H Z = Real.negMulLog (prb Z true) + Real.negMulLog (prb Z false) := by
        unfold H
        rw [Fintype.sum_bool]
      have hfalse : prb Z false = 1 - prb Z true := by linarith
      have hhalf : Real.negMulLog (1 / 2 : ℝ) = Real.log 2 / 2 := by
        unfold Real.negMulLog
        rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
        ring
      constructor
      · intro heq
        by_contra hne
        have hxy : prb Z true ≠ prb Z false := by
          rw [hfalse]
          intro h
          exact hne (by linarith)
        have hsc := Real.strictConcaveOn_negMulLog.2 (Set.mem_Ici.mpr (hnn true))
          (Set.mem_Ici.mpr (hnn false)) hxy (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
          (by norm_num)
        rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at hsc
        have hmid : (1/2 : ℝ) * prb Z true + (1/2 : ℝ) * prb Z false = 1/2 := by linarith
        rw [hmid, hhalf] at hsc
        rw [hHZ] at heq
        linarith
      · intro hp
        rw [hHZ, hp, hfalse, hp, show (1 : ℝ) - 1/2 = 1/2 by norm_num, hhalf]
        ring
    -- (3) mutual information never exceeds the fork's entropy
    have hle : mutualInfo W Z ≤ H Z := by
      have hcard : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by
        have := Fintype.card_pos (α := (Equiv.Perm (Fin n)))
        exact_mod_cast this
      have hjfib : ∀ (k : Bool) (b : Bool),
          fiber (joint W Z) (k, b) = (fiber W k).filter (fun ω => Z ω = b) := by
        intro k b
        unfold fiber joint
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro ω _
        simp [Prod.ext_iff]
      have hjfib2 : ∀ (k : Bool) (b : Bool),
          fiber (joint W Z) (k, b) = (fiber Z b).filter (fun ω => W ω = k) := by
        intro k b
        unfold fiber joint
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro ω _
        simp [Prod.ext_iff]
        tauto
      have hcm1 : ∀ k : Bool, ∑ b : Bool, (fiber (joint W Z) (k, b)).card = (fiber W k).card := by
        intro k
        have h := Finset.card_eq_sum_card_fiberwise
          (f := Z) (s := fiber W k) (t := (Finset.univ : Finset Bool)) (fun x _ => Finset.mem_univ (Z x))
        rw [h]
        exact Finset.sum_congr rfl (fun b _ => by rw [hjfib k b])
      have hcm2 : ∀ b : Bool, ∑ k : Bool, (fiber (joint W Z) (k, b)).card = (fiber Z b).card := by
        intro b
        have h := Finset.card_eq_sum_card_fiberwise
          (f := W) (s := fiber Z b) (t := (Finset.univ : Finset Bool)) (fun x _ => Finset.mem_univ (W x))
        rw [h]
        exact Finset.sum_congr rfl (fun k _ => by rw [hjfib2 k b])
      have hmarg1 : ∀ k : Bool, ∑ b : Bool, prb (joint W Z) (k, b) = prb W k := by
        intro k
        unfold prb
        rw [← Finset.sum_div]
        have hc : ∑ b : Bool, ((fiber (joint W Z) (k, b)).card : ℝ) = ((fiber W k).card : ℝ) := by
          have h := hcm1 k
          exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h
        rw [hc]
      have hmarg2 : ∀ b : Bool, ∑ k : Bool, prb (joint W Z) (k, b) = prb Z b := by
        intro b
        unfold prb
        rw [← Finset.sum_div]
        have hc : ∑ k : Bool, ((fiber (joint W Z) (k, b)).card : ℝ) = ((fiber Z b).card : ℝ) := by
          have h := hcm2 b
          exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h
        rw [hc]
      have hnnW : ∀ k : Bool, 0 ≤ prb W k := by
        intro k
        unfold prb
        positivity
      have hnnZ : ∀ b : Bool, 0 ≤ prb Z b := by
        intro b
        unfold prb
        positivity
      have hnnJ : ∀ p : Bool × Bool, 0 ≤ prb (joint W Z) p := by
        intro p
        unfold prb
        positivity
      have hsumW : ∑ k : Bool, prb W k = 1 := by
        unfold prb
        rw [← Finset.sum_div]
        have hc : ∑ k : Bool, ((fiber W k).card : ℝ) = (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
          have h := Finset.card_eq_sum_card_fiberwise
            (f := W) (s := (Finset.univ : Finset (Equiv.Perm (Fin n)))) (t := (Finset.univ : Finset Bool))
            (fun x _ => Finset.mem_univ (W x))
          rw [Finset.card_univ] at h
          have h2 : ∑ k : Bool, (fiber W k).card = Fintype.card (Equiv.Perm (Fin n)) := by
            unfold fiber
            exact h.symm
          exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h2
        rw [hc]
        field_simp
      have hsumZ : ∑ b : Bool, prb Z b = 1 := by
        unfold prb
        rw [← Finset.sum_div]
        have hc : ∑ b : Bool, ((fiber Z b).card : ℝ) = (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
          have h := Finset.card_eq_sum_card_fiberwise
            (f := Z) (s := (Finset.univ : Finset (Equiv.Perm (Fin n)))) (t := (Finset.univ : Finset Bool))
            (fun x _ => Finset.mem_univ (Z x))
          rw [Finset.card_univ] at h
          have h2 : ∑ b : Bool, (fiber Z b).card = Fintype.card (Equiv.Perm (Fin n)) := by
            unfold fiber
            exact h.symm
          exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h2
        rw [hc]
        field_simp
      have hle1 : ∀ (k : Bool) (b : Bool), prb (joint W Z) (k, b) ≤ prb W k := by
        intro k b
        rw [← hmarg1 k]
        exact Finset.single_le_sum (fun b' _ => hnnJ (k, b')) (Finset.mem_univ b)
      have hle2 : ∀ (k : Bool) (b : Bool), prb (joint W Z) (k, b) ≤ prb Z b := by
        intro k b
        rw [← hmarg2 b]
        exact Finset.single_le_sum (fun k' _ => hnnJ (k', b)) (Finset.mem_univ k)
      -- the mutual information as a KL divergence against the product
      have hident : mutualInfo W Z
          = ∑ p : Bool × Bool, prb (joint W Z) p
              * Real.log (prb (joint W Z) p / (prb W p.1 * prb Z p.2)) := by
        have hHW : H W = ∑ k : Bool, ∑ b : Bool, -(prb (joint W Z) (k, b) * Real.log (prb W k)) := by
          unfold H
          refine Finset.sum_congr rfl (fun k _ => ?_)
          have e : ∑ b : Bool, -(prb (joint W Z) (k, b) * Real.log (prb W k))
              = -((∑ b : Bool, prb (joint W Z) (k, b)) * Real.log (prb W k)) := by
            rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
          rw [e, hmarg1 k]
          unfold Real.negMulLog
          ring
        have hHZ : H Z = ∑ k : Bool, ∑ b : Bool, -(prb (joint W Z) (k, b) * Real.log (prb Z b)) := by
          unfold H
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          have e : ∑ k : Bool, -(prb (joint W Z) (k, b) * Real.log (prb Z b))
              = -((∑ k : Bool, prb (joint W Z) (k, b)) * Real.log (prb Z b)) := by
            rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
          rw [e, hmarg2 b]
          unfold Real.negMulLog
          ring
        have hHJ : H (joint W Z)
            = ∑ k : Bool, ∑ b : Bool, -(prb (joint W Z) (k, b) * Real.log (prb (joint W Z) (k, b))) := by
          unfold H
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun b _ => by
            unfold Real.negMulLog
            ring))
        unfold mutualInfo
        rw [hHW, hHZ, hHJ, Fintype.sum_prod_type]
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rcases eq_or_lt_of_le (hnnJ (k, b)) with h0 | h0
        · rw [← h0]
          simp
        · have hx : 0 < prb W k := lt_of_lt_of_le h0 (hle1 k b)
          have hy : 0 < prb Z b := lt_of_lt_of_le h0 (hle2 k b)
          rw [Real.log_div (ne_of_gt h0) (by positivity), Real.log_mul (ne_of_gt hx) (ne_of_gt hy)]
          ring
      -- the joint entropy dominates the marginal entropy, termwise
      have hHW : H W = ∑ k : Bool, ∑ b : Bool, -(prb (joint W Z) (k, b) * Real.log (prb W k)) := by
        unfold H
        refine Finset.sum_congr rfl (fun k _ => ?_)
        have e : ∑ b : Bool, -(prb (joint W Z) (k, b) * Real.log (prb W k))
            = -((∑ b : Bool, prb (joint W Z) (k, b)) * Real.log (prb W k)) := by
          rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
        rw [e, hmarg1 k]
        unfold Real.negMulLog
        ring
      have hHJ : H (joint W Z)
          = ∑ k : Bool, ∑ b : Bool, -(prb (joint W Z) (k, b) * Real.log (prb (joint W Z) (k, b))) := by
        unfold H
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun b _ => by
          unfold Real.negMulLog
          ring))
      have hmono : H W ≤ H (joint W Z) := by
        rw [hHW, hHJ]
        refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun b _ => ?_))
        rcases eq_or_lt_of_le (hnnJ (k, b)) with h0 | h0
        · rw [← h0]
          simp
        · have hx : 0 < prb W k := lt_of_lt_of_le h0 (hle1 k b)
          have hlog : Real.log (prb (joint W Z) (k, b)) ≤ Real.log (prb W k) :=
            Real.log_le_log h0 (hle1 k b)
          have := mul_le_mul_of_nonneg_left hlog (le_of_lt h0)
          linarith
      have hgoal : mutualInfo W Z = H W + H Z - H (joint W Z) := rfl
      rw [hgoal]
      linarith [hmono]
    -- (4) a Bool statistic has entropy at most log 2
    have hcb : ∀ Z : (Equiv.Perm (Fin n)) → Bool, H Z ≤ Real.log (Fintype.card Bool) := by
      intro Z
      have hOm : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      have hnnZ : ∀ k : Bool, 0 ≤ prb Z k := by
        intro k
        unfold prb
        positivity
      have hsumZ : ∑ k : Bool, prb Z k = 1 := by
        simp only [prb, fiber]
        rw [← Finset.sum_div, div_eq_one_iff_eq hOm, ← Nat.cast_sum]
        congr 1
        rw [← Finset.card_univ (α := (Equiv.Perm (Fin n)))]
        exact (Finset.card_eq_sum_card_fiberwise
          (fun ω _ => Finset.mem_coe.mpr (Finset.mem_univ _))).symm
      have hne : Nonempty Bool := ⟨Z (Classical.arbitrary (Equiv.Perm (Fin n)))⟩
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
    have hlog : H Z ≤ Real.log 2 := by
      have h := hcb Z
      simpa using h
    constructor
    · intro h
      have hge : Real.log 2 ≤ H Z := by rw [← h]; exact hle
      have hHZ : H Z = Real.log 2 := le_antisymm hlog hge
      exact ⟨hpin.mp (by rw [h, hHZ]), hbool.mp hHZ⟩
    · rintro ⟨hdet, hbal⟩
      rw [hpin.mpr hdet, hbool.mpr hbal]
  -- (B) a determined, balanced fork is the sign or its negation, re-proved inline
  have hdb : ∀ Z : Equiv.Perm (Fin n) → Bool,
      Determines (signBool : Equiv.Perm (Fin n) → Bool) Z → prb Z true = 1 / 2 →
      (Z = (signBool : Equiv.Perm (Fin n) → Bool) ∨
        Z = fun σ : Equiv.Perm (Fin n) => !(signBool σ)) := by
    intro Z hdet hbal
    have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    -- an even and an odd permutation
    have hi : (0 : ℕ) < n := by omega
    have hj : (1 : ℕ) < n := by omega
    set i : Fin n := ⟨0, hi⟩ with hidef
    set j : Fin n := ⟨1, hj⟩ with hjdef
    have hij : i ≠ j := by
      simp only [hidef, hjdef, Ne, Fin.mk.injEq]
      omega
    have hsb1 : signBool (1 : Equiv.Perm (Fin n)) = true := by
      simp [signBool]
    have hsbc : signBool (Equiv.swap i j) = false := by
      rw [signBool, Equiv.Perm.sign_swap hij]
      decide
    -- Z factors through the sign
    have hZ : ∀ σ : Equiv.Perm (Fin n),
        Z σ = if signBool σ = true then Z 1 else Z (Equiv.swap i j) := by
      intro σ
      by_cases h : signBool σ = true
      · rw [if_pos h]
        exact hdet σ 1 (by rw [h, hsb1])
      · rw [if_neg h]
        rw [Bool.not_eq_true] at h
        exact hdet σ (Equiv.swap i j) (by rw [h, hsbc])
    rcases Bool.eq_false_or_eq_true (Z 1) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (Z (Equiv.swap i j)) with h2 | h2
    · -- Z 1 = true, Z c = true : constantly true, so prb Z true = 1
      exfalso
      have hconst : ∀ σ, Z σ = true := by
        intro σ
        rw [hZ σ]
        by_cases h : signBool σ = true
        · rw [if_pos h]; exact h1
        · rw [if_neg h]; exact h2
      have he : fiber Z true = Finset.univ := by
        ext σ
        simp [fiber, hconst σ]
      rw [prb, he, Finset.card_univ, div_self hcard] at hbal
      norm_num at hbal
    · -- Z 1 = true, Z c = false : Z = signBool
      left
      funext σ
      rw [hZ σ]
      by_cases h : signBool σ = true
      · rw [if_pos h, h1, h]
      · rw [if_neg h, h2]
        rw [Bool.not_eq_true] at h
        rw [h]
    · -- Z 1 = false, Z c = true : Z = !signBool
      right
      funext σ
      rw [hZ σ]
      by_cases h : signBool σ = true
      · rw [if_pos h, h1, h]
        decide
      · rw [if_neg h, h2]
        rw [Bool.not_eq_true] at h
        rw [h]
        decide
    · -- Z 1 = false, Z c = false : constantly false, so prb Z true = 0
      exfalso
      have hconst : ∀ σ, Z σ = false := by
        intro σ
        rw [hZ σ]
        by_cases h : signBool σ = true
        · rw [if_pos h]; exact h1
        · rw [if_neg h]; exact h2
      have he : fiber Z true = ∅ := by
        ext σ
        simp [fiber, hconst σ]
      rw [prb, he] at hbal
      norm_num at hbal
  -- (C) the sign fork is balanced: multiplying by a transposition swaps the two fibres
  have hi : (0 : ℕ) < n := by omega
  have hj : (1 : ℕ) < n := by omega
  have hij : (⟨0, hi⟩ : Fin n) ≠ ⟨1, hj⟩ := by
    simp only [Ne, Fin.mk.injEq]
    omega
  have hcard0 : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hflip : ∀ a : Equiv.Perm (Fin n),
      signBool (a * Equiv.swap (⟨0, hi⟩ : Fin n) ⟨1, hj⟩) = !(signBool a) := by
    intro a
    have hs : Equiv.Perm.sign (a * Equiv.swap (⟨0, hi⟩ : Fin n) ⟨1, hj⟩)
        = -Equiv.Perm.sign a := by
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
      simp
    simp only [signBool, hs]
    rcases Int.units_eq_one_or (Equiv.Perm.sign a) with h | h <;> rw [h] <;> decide
  have hbij : (univ.filter (fun σ : Equiv.Perm (Fin n) => signBool σ = true)).card
      = (univ.filter (fun σ : Equiv.Perm (Fin n) => signBool σ = false)).card := by
    refine Finset.card_bij'
      (fun σ _ => σ * Equiv.swap (⟨0, hi⟩ : Fin n) ⟨1, hj⟩)
      (fun τ _ => τ * Equiv.swap (⟨0, hi⟩ : Fin n) ⟨1, hj⟩) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [hflip a, ha]
      rfl
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [hflip a, ha]
      rfl
    · intro a _
      simp [mul_assoc, Equiv.swap_mul_self]
    · intro a _
      simp [mul_assoc, Equiv.swap_mul_self]
  have hnotfilter : (univ.filter (fun σ : Equiv.Perm (Fin n) => ¬ (signBool σ = true)))
      = (univ.filter (fun σ : Equiv.Perm (Fin n) => signBool σ = false)) := by
    apply Finset.filter_congr
    intro σ _
    simp
  have hsplit : (univ.filter (fun σ : Equiv.Perm (Fin n) => signBool σ = true)).card
      + (univ.filter (fun σ : Equiv.Perm (Fin n) => signBool σ = false)).card
      = Fintype.card (Equiv.Perm (Fin n)) := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Equiv.Perm (Fin n)))) (p := fun σ => signBool σ = true)
    rw [Finset.card_univ] at h
    rw [← hnotfilter]
    exact h
  have hcnat : 2 * (univ.filter (fun σ : Equiv.Perm (Fin n) => signBool σ = true)).card
      = Fintype.card (Equiv.Perm (Fin n)) := by omega
  have hcR : (2 : ℝ) * ((univ.filter (fun σ : Equiv.Perm (Fin n) => signBool σ = true)).card : ℝ)
      = (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by exact_mod_cast hcnat
  have hhalf : prb (signBool : Equiv.Perm (Fin n) → Bool) true = 1 / 2 := by
    simp only [prb, fiber]
    rw [div_eq_div_iff hcard0 (by norm_num : (2 : ℝ) ≠ 0)]
    linarith
  have hhalf' : prb (fun σ : Equiv.Perm (Fin n) => !(signBool σ)) true = 1 / 2 := by
    have hfe : (univ.filter (fun σ : Equiv.Perm (Fin n) => (!(signBool σ)) = true))
        = (univ.filter (fun σ : Equiv.Perm (Fin n) => signBool σ = false)) := by
      apply Finset.filter_congr
      intro σ _
      simp
    simp only [prb, fiber]
    rw [hfe, ← hbij, div_eq_div_iff hcard0 (by norm_num : (2 : ℝ) ≠ 0)]
    linarith
  constructor
  · intro h
    obtain ⟨hdet, hbal⟩ := (hcap (signBool : Equiv.Perm (Fin n) → Bool) Y).mp h
    exact hdb Y hdet hbal
  · rintro (rfl | rfl)
    · exact (hcap (signBool : Equiv.Perm (Fin n) → Bool) _).mpr ⟨fun _ _ h => h, hhalf⟩
    · exact (hcap (signBool : Equiv.Perm (Fin n) → Bool) _).mpr
        ⟨fun _ _ h => by simp [h], hhalf'⟩
