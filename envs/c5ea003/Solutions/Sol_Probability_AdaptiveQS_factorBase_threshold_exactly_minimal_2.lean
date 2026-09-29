-- Prove2me | solution 2 for Probability.AdaptiveQS.factorBase_threshold_exactly_minimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T20:04:49.651953+00:00
-- url     : https://prove2.me/submissions/fb02b8b1-6388-408f-b5f1-0a5152a3f798

import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSPrefixOptimality
import Definitions.Def_Probability_AdaptiveQSResidueRate
import Definitions.Def_Probability_AdaptiveQSSkipFlip
import Definitions.Def_Probability_AdaptiveQSTieSlack

open Probability.AdaptiveQS Finset in
theorem solution {N : ℤ} {FB : Finset ℕ} {Q : ℝ}
    (hFB : AdmissibleFB N FB) (hQ : 0 < Q)
    (hfeas : ∃ K ⊆ FB, Q ≤ ∑ p ∈ K, periodRate N p) :
    ∃ θ : ℝ,
      Q ≤ ∑ p ∈ keepSet FB (periodRate N) θ, periodRate N p ∧
      (∀ K ⊆ FB, Q ≤ ∑ p ∈ K, periodRate N p →
        (keepSet FB (periodRate N) θ).card ≤ K.card) ∧
      throughput FB (periodRate N)
        ≤ throughput (keepSet FB (periodRate N) θ) (periodRate N) := by
  classical
  have skipcore : ∀ {s : Finset ℕ} {d r : ℕ → ℝ}, Concordant s d r → ∀ θ : ℝ,
      (keepSet s d θ).Nonempty → throughput s r ≤ throughput (keepSet s d θ) r := by
    intro s d r hc θ hK
    have hsplit : s = keepSet s d θ ∪ skipSet s d θ := by
      ext i
      simp only [keepSet, skipSet, Finset.mem_union, Finset.mem_filter]
      tauto
    have hdisj : Disjoint (keepSet s d θ) (skipSet s d θ) := by
      rw [keepSet, skipSet]
      exact Finset.disjoint_filter.2 (fun i _ h1 h2 => h2 h1)
    have hcmp : ∀ i ∈ keepSet s d θ, ∀ j ∈ skipSet s d θ, r j ≤ r i := by
      intro i hi j hj
      rw [keepSet, Finset.mem_filter] at hi
      rw [skipSet, Finset.mem_filter] at hj
      exact hc i hi.1 j hj.1 (by linarith [not_le.1 hj.2])
    -- double counting: |K| Σ_S r ≤ |S| Σ_K r
    have hdouble : ((keepSet s d θ).card : ℝ) * ∑ j ∈ skipSet s d θ, r j
        ≤ ((skipSet s d θ).card : ℝ) * ∑ i ∈ keepSet s d θ, r i := by
      have h1 : ((keepSet s d θ).card : ℝ) * ∑ j ∈ skipSet s d θ, r j
          = ∑ i ∈ keepSet s d θ, ∑ j ∈ skipSet s d θ, r j := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have h2 : ((skipSet s d θ).card : ℝ) * ∑ i ∈ keepSet s d θ, r i
          = ∑ i ∈ keepSet s d θ, ∑ j ∈ skipSet s d θ, r i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [h1, h2]
      exact Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hcmp i hi j hj))
    have hKpos : (0 : ℝ) < (keepSet s d θ).card := by exact_mod_cast hK.card_pos
    unfold throughput
    rw [hsplit, Finset.sum_union hdisj, Finset.card_union_of_disjoint hdisj]
    have hkeep : keepSet (keepSet s d θ ∪ skipSet s d θ) d θ = keepSet s d θ := by
      ext i
      simp only [keepSet, skipSet, Finset.mem_union, Finset.mem_filter]
      tauto
    rw [hkeep]
    push_cast
    have hden : (0 : ℝ) < ((keepSet s d θ).card : ℝ) + ((skipSet s d θ).card : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) (skipSet s d θ).card
      linarith
    rw [div_le_div_iff₀ hden hKpos]
    nlinarith [hdouble]
  -- the per-period rate of an admissible prime is `2 / p`
  have hrate : ∀ p ∈ FB, periodRate N p = 2 / p := by
    intro p hp
    obtain ⟨hpP, hp2, hN0, a, ha⟩ := hFB p hp
    haveI := Fact.mk hpP
    have hsol : ∀ x : ℕ, x < p →
        ((p : ℤ) ∣ ((x : ℤ) ^ 2 - N) ↔ x = a.val ∨ x = (-a).val) := by
      intro x hx
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ha, sub_eq_zero]
      constructor
      · intro h
        have hm : ((x : ZMod p) - a) * ((x : ZMod p) + a) = 0 := by linear_combination h
        rcases mul_eq_zero.1 hm with h1 | h1
        · left
          have e : (x : ZMod p) = a := sub_eq_zero.1 h1
          rw [← e, ZMod.val_natCast, Nat.mod_eq_of_lt hx]
        · right
          have e : (x : ZMod p) = -a := eq_neg_of_add_eq_zero_left h1
          rw [← e, ZMod.val_natCast, Nat.mod_eq_of_lt hx]
      · rintro (rfl | rfl)
        · rw [ZMod.natCast_zmod_val]
          ring
        · rw [ZMod.natCast_zmod_val]
          ring
    have hset : (Finset.range p).filter (fun x : ℕ => (p : ℤ) ∣ ((x : ℤ) ^ 2 - N))
        = {a.val, (-a).val} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hx, h⟩
        exact (hsol x hx).1 h
      · intro h
        have hx : x < p := by
          rcases h with rfl | rfl <;> exact ZMod.val_lt _
        exact ⟨hx, (hsol x hx).2 h⟩
    have hne : a.val ≠ (-a).val := by
      intro h
      have ha0 : a ≠ 0 := by
        rintro rfl
        apply hN0
        rw [ha]
        ring
      have e : a = -a := ZMod.val_injective p h
      have h2 : (2 : ZMod p) * a = 0 := by linear_combination e
      rcases mul_eq_zero.1 h2 with h3 | h3
      · have h4 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h3
        rw [CharP.cast_eq_zero_iff (ZMod p) p] at h4
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hpP Nat.prime_two).1 h4)
      · exact ha0 h3
    unfold periodRate
    rw [hset, Finset.card_pair hne]
    push_cast
    ring
  have hrpos : ∀ p ∈ FB, 0 < periodRate N p := by
    intro p hp
    rw [hrate p hp]
    have : (0 : ℝ) < p := by exact_mod_cast (hFB p hp).1.pos
    positivity
  have hrinj : ∀ p ∈ FB, ∀ q ∈ FB, periodRate N p = periodRate N q → p = q := by
    intro p hp q hq h
    rw [hrate p hp, hrate q hq] at h
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hFB p hp).1.pos
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (hFB q hq).1.pos
    rw [div_eq_div_iff hp0.ne' hq0.ne'] at h
    have : (p : ℝ) = q := by linarith
    exact_mod_cast this
  -- the full base is feasible and nonempty
  obtain ⟨K0, hK0FB, hK0Q⟩ := hfeas
  have hsumFB : Q ≤ ∑ p ∈ FB, periodRate N p :=
    hK0Q.trans (Finset.sum_le_sum_of_subset_of_nonneg hK0FB (fun p hp _ => (hrpos p hp).le))
  have hFBne : FB.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsumFB
    linarith
  -- the largest feasible rate threshold
  obtain ⟨T, hT⟩ : ∃ T : Finset ℝ, T = (FB.image (periodRate N)).filter
      (fun θ => Q ≤ ∑ p ∈ keepSet FB (periodRate N) θ, periodRate N p) := ⟨_, rfl⟩
  have hTne : T.Nonempty := by
    refine ⟨(FB.image (periodRate N)).min' (hFBne.image _), ?_⟩
    rw [hT, Finset.mem_filter]
    refine ⟨Finset.min'_mem _ _, ?_⟩
    have hk : keepSet FB (periodRate N) ((FB.image (periodRate N)).min' (hFBne.image _)) = FB := by
      ext p
      simp only [keepSet, Finset.mem_filter]
      constructor
      · exact fun h => h.1
      · exact fun hp => ⟨hp, Finset.min'_le _ _ (Finset.mem_image_of_mem _ hp)⟩
    rw [hk]
    exact hsumFB
  obtain ⟨θs, hθsdef⟩ : ∃ θ, θ = T.max' hTne := ⟨_, rfl⟩
  have hθsT : θs ∈ T := by rw [hθsdef]; exact Finset.max'_mem _ _
  have hθsT' := hθsT
  rw [hT, Finset.mem_filter] at hθsT'
  obtain ⟨hθsimg, hθsQ⟩ := hθsT'
  obtain ⟨ps, hpsFB, hps⟩ := Finset.mem_image.1 hθsimg
  have hθs0 : 0 < θs := by rw [← hps]; exact hrpos ps hpsFB
  refine ⟨θs, hθsQ, ?_, ?_⟩
  · intro K hKFB hKQ
    by_contra hlt
    rw [not_le] at hlt
    have hpsK : ps ∈ keepSet FB (periodRate N) θs := by
      simp only [keepSet, Finset.mem_filter]
      exact ⟨hpsFB, le_of_eq hps.symm⟩
    obtain ⟨K', hK'⟩ : ∃ K', K' = (keepSet FB (periodRate N) θs).erase ps := ⟨_, rfl⟩
    have hK'FB : K' ⊆ FB := by
      intro q hq
      rw [hK', Finset.mem_erase] at hq
      simp only [keepSet, Finset.mem_filter] at hq
      exact hq.2.1
    have hK'gt : ∀ q ∈ K', θs < periodRate N q := by
      intro q hq
      rw [hK', Finset.mem_erase] at hq
      simp only [keepSet, Finset.mem_filter] at hq
      rcases lt_or_eq_of_le hq.2.2 with h | h
      · exact h
      · exact absurd (hrinj q hq.2.1 ps hpsFB (by rw [hps, h])) hq.1
    have hout : ∀ q ∈ FB, q ∉ K' → periodRate N q ≤ θs := by
      intro q hq hqK
      by_cases hqps : q = ps
      · rw [hqps, hps]
      · by_contra h
        apply hqK
        rw [hK', Finset.mem_erase]
        simp only [keepSet, Finset.mem_filter]
        exact ⟨hqps, hq, (not_le.1 h).le⟩
    have hK'inf : ∑ q ∈ K', periodRate N q < Q := by
      by_cases hK'e : K'.Nonempty
      · obtain ⟨θ2, hθ2⟩ : ∃ θ2, θ2 = (K'.image (periodRate N)).min' (hK'e.image _) := ⟨_, rfl⟩
        have hθ2mem : θ2 ∈ K'.image (periodRate N) := by rw [hθ2]; exact Finset.min'_mem _ _
        obtain ⟨q2, hq2K', hq2⟩ := Finset.mem_image.1 hθ2mem
        have hθ2gt : θs < θ2 := by rw [← hq2]; exact hK'gt q2 hq2K'
        have hkeep2 : keepSet FB (periodRate N) θ2 = K' := by
          ext p
          simp only [keepSet, Finset.mem_filter]
          constructor
          · rintro ⟨hp, hpθ⟩
            by_contra hpK
            have := hout p hp hpK
            linarith
          · intro hp
            refine ⟨hK'FB hp, ?_⟩
            rw [hθ2]
            exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hp)
        have hθ2T : θ2 ∉ T := by
          intro h
          have := Finset.le_max' T θ2 h
          rw [← hθsdef] at this
          linarith
        rw [hT, Finset.mem_filter] at hθ2T
        have hθ2img : θ2 ∈ FB.image (periodRate N) := by
          rw [← hq2]
          exact Finset.mem_image_of_mem _ (hK'FB hq2K')
        have := fun h => hθ2T ⟨hθ2img, h⟩
        rw [hkeep2] at this
        exact not_le.1 this
      · rw [Finset.not_nonempty_iff_eq_empty] at hK'e
        rw [hK'e, Finset.sum_empty]
        exact hQ
    have hcardKK' : K.card ≤ K'.card := by
      rw [hK', Finset.card_erase_of_mem hpsK]
      omega
    have hexch : ∑ q ∈ K, periodRate N q ≤ ∑ q ∈ K', periodRate N q := by
      rw [← Finset.sum_inter_add_sum_diff K K', ← Finset.sum_inter_add_sum_diff K' K,
        Finset.inter_comm K' K]
      refine add_le_add le_rfl ?_
      have hc : (K \ K').card ≤ (K' \ K).card := by
        have h1 := Finset.card_sdiff_add_card_inter K K'
        have h2 := Finset.card_sdiff_add_card_inter K' K
        rw [Finset.inter_comm] at h2
        omega
      calc ∑ q ∈ K \ K', periodRate N q ≤ ∑ q ∈ K \ K', θs :=
            Finset.sum_le_sum (fun q hq =>
              hout q (hKFB (Finset.mem_sdiff.1 hq).1) (Finset.mem_sdiff.1 hq).2)
        _ = (K \ K').card * θs := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (K' \ K).card * θs := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hθs0.le
        _ = ∑ q ∈ K' \ K, θs := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ q ∈ K' \ K, periodRate N q :=
            Finset.sum_le_sum (fun q hq => (hK'gt q (Finset.mem_sdiff.1 hq).1).le)
    linarith
  · apply skipcore (fun i _ j _ h => h.le) θs
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hθsQ
    linarith
