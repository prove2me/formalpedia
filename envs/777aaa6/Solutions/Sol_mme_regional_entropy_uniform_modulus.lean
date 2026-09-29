-- Prove2me | solution 1 for mme_regional_entropy_uniform_modulus
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T20:34:03.153699+00:00
-- url     : https://prove2.me/submissions/1d44d446-861c-4334-8119-e6a11184a40a

import Definitions.Def_mme_regional_entropy_rate_data
import Mathlib

open BigOperators MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

private theorem entropy_continuous {W : Type*} [Fintype W] :
    Continuous (entropy (W := W)) := by
  unfold entropy
  exact continuous_finset_sum _ (fun w _ ↦ Real.continuous_negMulLog.comp (continuous_apply w))

theorem solution {W : Type*} [Fintype W] :
    (∀ eps : ℝ, 0 ≤ eps → 0 ≤ entropyModulus W eps) ∧
    (∀ (eps : ℝ) (p q : W → ℝ), (∀ w, p w ∈ Set.Icc 0 1) →
      (∀ w, q w ∈ Set.Icc 0 1) → (∀ w, |p w - q w| ≤ eps) →
      |entropy p - entropy q| ≤ entropyModulus W eps) ∧
    (∀ delta : ℝ, 0 < delta → ∃ eps : ℝ, 0 < eps ∧
      ∀ e : ℝ, 0 ≤ e → e ≤ eps → entropyModulus W e ≤ delta) := by
  classical
  let box : Set (W → ℝ) := Set.pi Set.univ (fun _ ↦ Set.Icc 0 1)
  have hb : IsCompact box := isCompact_univ_pi (fun _ ↦ isCompact_Icc)
  have hcont : Continuous (fun z : (W → ℝ) × (W → ℝ) ↦ |entropy z.1 - entropy z.2|) :=
    ((entropy_continuous.comp continuous_fst).sub (entropy_continuous.comp continuous_snd)).abs
  have hbounded : BddAbove ((fun z : (W → ℝ) × (W → ℝ) ↦ |entropy z.1 - entropy z.2|) '' (box ×ˢ box)) :=
    ((hb.prod hb).image hcont).bddAbove
  have hm (e : ℝ) : BddAbove {z : ℝ | ∃ p q : W → ℝ,
      (∀ w, p w ∈ Set.Icc 0 1) ∧ (∀ w, q w ∈ Set.Icc 0 1) ∧
      (∀ w, |p w - q w| ≤ e) ∧ z = |entropy p - entropy q|} := by
    apply hbounded.mono
    rintro z ⟨p,q,hp,hq,he,rfl⟩
    refine ⟨(p,q),?_,rfl⟩
    simpa only [box,Set.mem_prod,Set.mem_pi,Set.mem_univ,forall_true_left] using And.intro hp hq
  have hzero (e : ℝ) (he : 0 ≤ e) : 0 ∈ {z : ℝ | ∃ p q : W → ℝ,
      (∀ w, p w ∈ Set.Icc 0 1) ∧ (∀ w, q w ∈ Set.Icc 0 1) ∧
      (∀ w, |p w - q w| ≤ e) ∧ z = |entropy p - entropy q|} := by
    exact ⟨fun _ ↦ 0,fun _ ↦ 0,fun _ ↦ ⟨le_rfl,zero_le_one⟩,
      fun _ ↦ ⟨le_rfl,zero_le_one⟩,by simpa using fun _ : W ↦ he,by simp⟩
  refine ⟨fun e he ↦ le_csSup (hm e) (hzero e he),?_,?_⟩
  · intro e p q hp hq he
    exact le_csSup (hm e) ⟨p,q,hp,hq,he,rfl⟩
  · intro delta hd
    have hu := hb.uniformContinuousOn_of_continuous entropy_continuous.continuousOn
    obtain ⟨eps,heps,hu⟩ := Metric.uniformContinuousOn_iff.mp hu delta hd
    refine ⟨eps / 2,half_pos heps,fun e he hsmall ↦ ?_⟩
    apply csSup_le ⟨0,hzero e he⟩
    rintro z ⟨p,q,hp,hq,hpq,rfl⟩
    have hp' : p ∈ box := by simpa only [box,Set.mem_pi,Set.mem_univ,forall_true_left] using hp
    have hq' : q ∈ box := by simpa only [box,Set.mem_pi,Set.mem_univ,forall_true_left] using hq
    have hdist : dist p q < eps := by
      apply (dist_pi_lt_iff heps).mpr
      intro w
      rw [Real.dist_eq]
      exact (hpq w).trans_lt (hsmall.trans_lt (half_lt_self heps))
    simpa only [Real.dist_eq] using (hu p hp' q hq' hdist).le
