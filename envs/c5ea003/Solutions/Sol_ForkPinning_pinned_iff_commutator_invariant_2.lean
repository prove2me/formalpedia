-- Prove2me | solution 2 for ForkPinning.pinned_iff_commutator_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T23:22:34.446373+00:00
-- url     : https://prove2.me/submissions/c8bc2b54-96ef-43a1-9fe9-e07c164f6e1a

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningGalois
open ForkPinning Finset Real in
theorem solution {G : Type*} [Group G] {β : Type*} [Fintype G] [Nonempty G]
    [Fintype β] [DecidableEq β] [Fintype (Abelianization G)] [DecidableEq (Abelianization G)]
    (Y : G → β) :
    mutualInfo (fun g : G => Abelianization.of g) Y = H Y
      ↔ ∀ g c, c ∈ commutator G → Y (g * c) = Y g := by
  -- (1) pinning is exactly determination (re-proved inline)
  have hpin : ∀ X : G → Abelianization G, mutualInfo X Y = H Y ↔ Determines X Y := by
    intro X
    have hcard : (0 : ℝ) < Fintype.card G := by
      have := Fintype.card_pos (α := G)
      exact_mod_cast this
    have hjfib : ∀ (k : (Abelianization G)) (b : β),
        fiber (joint X Y) (k, b) = (fiber X k).filter (fun ω => Y ω = b) := by
      intro k b
      unfold fiber joint
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro ω _
      simp [Prod.ext_iff]
    have hjfib2 : ∀ (k : (Abelianization G)) (b : β),
        fiber (joint X Y) (k, b) = (fiber Y b).filter (fun ω => X ω = k) := by
      intro k b
      unfold fiber joint
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro ω _
      simp [Prod.ext_iff]
      tauto
    have hcm1 : ∀ k : (Abelianization G), ∑ b : β, (fiber (joint X Y) (k, b)).card = (fiber X k).card := by
      intro k
      have h := Finset.card_eq_sum_card_fiberwise
        (f := Y) (s := fiber X k) (t := (Finset.univ : Finset β)) (fun x _ => Finset.mem_univ (Y x))
      rw [h]
      exact Finset.sum_congr rfl (fun b _ => by rw [hjfib k b])
    have hcm2 : ∀ b : β, ∑ k : (Abelianization G), (fiber (joint X Y) (k, b)).card = (fiber Y b).card := by
      intro b
      have h := Finset.card_eq_sum_card_fiberwise
        (f := X) (s := fiber Y b) (t := (Finset.univ : Finset (Abelianization G))) (fun x _ => Finset.mem_univ (X x))
      rw [h]
      exact Finset.sum_congr rfl (fun k _ => by rw [hjfib2 k b])
    have hmarg1 : ∀ k : (Abelianization G), ∑ b : β, prb (joint X Y) (k, b) = prb X k := by
      intro k
      unfold prb
      rw [← Finset.sum_div]
      have hc : ∑ b : β, ((fiber (joint X Y) (k, b)).card : ℝ) = ((fiber X k).card : ℝ) := by
        have h := hcm1 k
        exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h
      rw [hc]
    have hmarg2 : ∀ b : β, ∑ k : (Abelianization G), prb (joint X Y) (k, b) = prb Y b := by
      intro b
      unfold prb
      rw [← Finset.sum_div]
      have hc : ∑ k : (Abelianization G), ((fiber (joint X Y) (k, b)).card : ℝ) = ((fiber Y b).card : ℝ) := by
        have h := hcm2 b
        exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h
      rw [hc]
    have hnnX : ∀ k : (Abelianization G), 0 ≤ prb X k := by
      intro k
      unfold prb
      positivity
    have hnnY : ∀ b : β, 0 ≤ prb Y b := by
      intro b
      unfold prb
      positivity
    have hnnJ : ∀ p : (Abelianization G) × β, 0 ≤ prb (joint X Y) p := by
      intro p
      unfold prb
      positivity
    have hsumX : ∑ k : (Abelianization G), prb X k = 1 := by
      unfold prb
      rw [← Finset.sum_div]
      have hc : ∑ k : (Abelianization G), ((fiber X k).card : ℝ) = (Fintype.card G : ℝ) := by
        have h := Finset.card_eq_sum_card_fiberwise
          (f := X) (s := (Finset.univ : Finset G)) (t := (Finset.univ : Finset (Abelianization G)))
          (fun x _ => Finset.mem_univ (X x))
        rw [Finset.card_univ] at h
        have h2 : ∑ k : (Abelianization G), (fiber X k).card = Fintype.card G := by
          unfold fiber
          exact h.symm
        exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h2
      rw [hc]
      field_simp
    have hsumY : ∑ b : β, prb Y b = 1 := by
      unfold prb
      rw [← Finset.sum_div]
      have hc : ∑ b : β, ((fiber Y b).card : ℝ) = (Fintype.card G : ℝ) := by
        have h := Finset.card_eq_sum_card_fiberwise
          (f := Y) (s := (Finset.univ : Finset G)) (t := (Finset.univ : Finset β))
          (fun x _ => Finset.mem_univ (Y x))
        rw [Finset.card_univ] at h
        have h2 : ∑ b : β, (fiber Y b).card = Fintype.card G := by
          unfold fiber
          exact h.symm
        exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) h2
      rw [hc]
      field_simp
    have hle1 : ∀ (k : (Abelianization G)) (b : β), prb (joint X Y) (k, b) ≤ prb X k := by
      intro k b
      rw [← hmarg1 k]
      exact Finset.single_le_sum (fun b' _ => hnnJ (k, b')) (Finset.mem_univ b)
    have hle2 : ∀ (k : (Abelianization G)) (b : β), prb (joint X Y) (k, b) ≤ prb Y b := by
      intro k b
      rw [← hmarg2 b]
      exact Finset.single_le_sum (fun k' _ => hnnJ (k', b)) (Finset.mem_univ k)
    -- the mutual information as a KL divergence against the product
    have hident : mutualInfo X Y
        = ∑ p : (Abelianization G) × β, prb (joint X Y) p
            * Real.log (prb (joint X Y) p / (prb X p.1 * prb Y p.2)) := by
      have hHX : H X = ∑ k : (Abelianization G), ∑ b : β, -(prb (joint X Y) (k, b) * Real.log (prb X k)) := by
        unfold H
        refine Finset.sum_congr rfl (fun k _ => ?_)
        have e : ∑ b : β, -(prb (joint X Y) (k, b) * Real.log (prb X k))
            = -((∑ b : β, prb (joint X Y) (k, b)) * Real.log (prb X k)) := by
          rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
        rw [e, hmarg1 k]
        unfold Real.negMulLog
        ring
      have hHY : H Y = ∑ k : (Abelianization G), ∑ b : β, -(prb (joint X Y) (k, b) * Real.log (prb Y b)) := by
        unfold H
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        have e : ∑ k : (Abelianization G), -(prb (joint X Y) (k, b) * Real.log (prb Y b))
            = -((∑ k : (Abelianization G), prb (joint X Y) (k, b)) * Real.log (prb Y b)) := by
          rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
        rw [e, hmarg2 b]
        unfold Real.negMulLog
        ring
      have hHJ : H (joint X Y)
          = ∑ k : (Abelianization G), ∑ b : β, -(prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b))) := by
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
    have hHX : H X = ∑ k : (Abelianization G), ∑ b : β, -(prb (joint X Y) (k, b) * Real.log (prb X k)) := by
      unfold H
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have e : ∑ b : β, -(prb (joint X Y) (k, b) * Real.log (prb X k))
          = -((∑ b : β, prb (joint X Y) (k, b)) * Real.log (prb X k)) := by
        rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      rw [e, hmarg1 k]
      unfold Real.negMulLog
      ring
    have hHJ : H (joint X Y)
        = ∑ k : (Abelianization G), ∑ b : β, -(prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b))) := by
      unfold H
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun b _ => by
        unfold Real.negMulLog
        ring))
    have hposJ : ∀ ω : G, 0 < prb (joint X Y) (X ω, Y ω) := by
      intro ω
      unfold prb
      have hmem : ω ∈ fiber (joint X Y) (X ω, Y ω) := by
        unfold fiber joint
        simp
      have hc : 0 < ((fiber (joint X Y) (X ω, Y ω)).card : ℝ) := by
        have := Finset.card_pos.mpr ⟨ω, hmem⟩
        exact_mod_cast this
      exact div_pos hc hcard
    have hposX : ∀ ω : G, 0 < prb X (X ω) := by
      intro ω
      unfold prb
      have hmem : ω ∈ fiber X (X ω) := by
        unfold fiber
        simp
      have hc : 0 < ((fiber X (X ω)).card : ℝ) := by
        have := Finset.card_pos.mpr ⟨ω, hmem⟩
        exact_mod_cast this
      exact div_pos hc hcard
    have htermle : ∀ (k : (Abelianization G)) (b : β),
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
  -- (2) determination by the abelianization is commutator invariance
  have hcomm : Determines (fun g : G => Abelianization.of g) Y
      ↔ ∀ g c, c ∈ commutator G → Y (g * c) = Y g := by
    constructor
    · intro hdet g c hc
      have hc1 : Abelianization.of c = 1 := by
        rw [← MonoidHom.mem_ker, Abelianization.ker_of]
        exact hc
      apply hdet
      simp only [map_mul, hc1, mul_one]
    · intro hinv g g' hg
      have hmem : g⁻¹ * g' ∈ commutator G := by
        rw [← Abelianization.ker_of, MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        simp only [hg]
        simp
      have hY := hinv g (g⁻¹ * g') hmem
      rw [mul_inv_cancel_left] at hY
      exact hY.symm
  exact (hpin _).trans hcomm
