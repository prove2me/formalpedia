-- Prove2me | solution 1 for BanditAlgorithm.bandit_divergence_one_step
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-26T01:41:10.112775+00:00
-- url     : https://prove2.me/submissions/e5c3f2ab-e884-4afd-a4ab-94e92ac25ff4

import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Definitions.Def_BanditPolicy

/-!
Lattimore--Szepesvari, *Bandit Algorithms*, Lemma 15.1 and Eq. (15.2),
printed pp. 198--199 / PDF pp. 207--208.

This slot81 scratch isolates the exact conditional one-round computation in
the divergence decomposition: after conditioning on the selected arm, the
KL divergence is the policy-weighted sum of the arm divergences.
-/

open MeasureTheory ProbabilityTheory InformationTheory

namespace Slot81DivergenceStepScratch

open BanditAlgorithm

private theorem arm_ac {k : ℕ} (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤) (i : Fin k) :
    nu.P i ≪ nu'.P i :=
  (klDiv_ne_top_iff.mp (hKL i)).1

private theorem measurable_arm_rnDeriv {k : ℕ} (nu nu' : StochasticBandit k) :
    Measurable (fun z : Fin k × ℝ ↦ (nu.P z.1).rnDeriv (nu'.P z.1) z.2) := by
  classical
  let f : Fin k × ℝ → ENNReal := fun z ↦
    ∑ i, Set.indicator {z : Fin k × ℝ | z.1 = i}
      (fun z ↦ (nu.P i).rnDeriv (nu'.P i) z.2) z
  have hf : Measurable f := by
    dsimp [f]
    apply Finset.measurable_sum
    intro i _
    exact ((Measure.measurable_rnDeriv (nu.P i) (nu'.P i)).comp measurable_snd).indicator
      ((measurableSet_singleton i).preimage measurable_fst)
  have h_eq : f = fun z : Fin k × ℝ ↦
      (nu.P z.1).rnDeriv (nu'.P z.1) z.2 := by
    funext z
    simp only [f, Set.indicator_apply, Set.mem_setOf_eq]
    rw [Finset.sum_ite_eq]
    simp
  rwa [← h_eq]

private theorem step_ac {k n : ℕ} (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) (h : BanditHistory k n) :
    banditStepKernel nu pi n h ≪ banditStepKernel nu' pi n h := by
  rw [banditStepKernel, banditStepKernel]
  rw [Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.compProd_apply_eq_compProd_sectR]
  refine Measure.AbsolutelyContinuous.compProd_right ?_
  filter_upwards [] with i
  simpa [Kernel.sectR_apply, banditRewardKernel] using arm_ac nu nu' hKL i

private theorem step_withDensity {k n : ℕ} (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) (h : BanditHistory k n) :
    (banditStepKernel nu' pi n h).withDensity
        (fun z : Fin k × ℝ ↦ (nu.P z.1).rnDeriv (nu'.P z.1) z.2) =
      banditStepKernel nu pi n h := by
  rw [banditStepKernel, banditStepKernel]
  rw [Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.compProd_apply_eq_compProd_sectR]
  ext s hs
  rw [withDensity_apply _ hs]
  rw [Measure.compProd_apply hs]
  rw [← lintegral_indicator hs]
  rw [Measure.lintegral_compProd
    ((measurable_arm_rnDeriv nu nu').indicator hs)]
  apply lintegral_congr
  intro i
  rw [Kernel.sectR_apply, Kernel.sectR_apply]
  simp only [Kernel.comap_apply, banditRewardKernel]
  change (∫⁻ x, s.indicator
      (fun z : Fin k × ℝ ↦ (nu.P z.1).rnDeriv (nu'.P z.1) z.2) (i, x)
      ∂nu'.P i) = nu.P i (Prod.mk i ⁻¹' s)
  calc
    _ = ∫⁻ x in Prod.mk i ⁻¹' s,
        (nu.P i).rnDeriv (nu'.P i) x ∂nu'.P i := by
      rw [← lintegral_indicator (measurable_prodMk_left hs)]
      apply lintegral_congr
      intro x
      rfl
    _ = nu.P i (Prod.mk i ⁻¹' s) :=
      Measure.setLIntegral_rnDeriv (arm_ac nu nu' hKL i) _

private theorem rnDeriv_step {k n : ℕ} (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) (h : BanditHistory k n) :
    (banditStepKernel nu pi n h).rnDeriv (banditStepKernel nu' pi n h) =ᵐ[
      banditStepKernel nu' pi n h]
        fun z : Fin k × ℝ ↦ (nu.P z.1).rnDeriv (nu'.P z.1) z.2 := by
  rw [← step_withDensity nu nu' hKL pi h]
  exact Measure.rnDeriv_withDensity _ (measurable_arm_rnDeriv nu nu')

private theorem klDiv_banditStepKernel_eq_sum {k n : ℕ}
    (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) (h : BanditHistory k n) :
    klDiv (banditStepKernel nu pi n h) (banditStepKernel nu' pi n h) =
      ∑ i, ENNReal.ofReal ((pi.select n h).real {i}) *
        klDiv (nu.P i) (nu'.P i) := by
  rw [klDiv_eq_lintegral_klFun_of_ac (step_ac nu nu' hKL pi h)]
  calc
    (∫⁻ z, ENNReal.ofReal
        (klFun (((banditStepKernel nu pi n h).rnDeriv
          (banditStepKernel nu' pi n h)) z).toReal)
        ∂banditStepKernel nu' pi n h) =
        ∫⁻ z, ENNReal.ofReal
          (klFun (((nu.P z.1).rnDeriv (nu'.P z.1) z.2).toReal))
          ∂banditStepKernel nu' pi n h := by
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_step nu nu' hKL pi h] with z hz
      rw [hz]
    _ = ∫⁻ i, klDiv (nu.P i) (nu'.P i) ∂pi.select n h := by
      rw [banditStepKernel]
      rw [Kernel.compProd_apply_eq_compProd_sectR]
      have hmeas : Measurable (fun z : Fin k × ℝ ↦ ENNReal.ofReal
          (klFun (((nu.P z.1).rnDeriv (nu'.P z.1) z.2).toReal))) :=
        ENNReal.measurable_ofReal.comp
          (measurable_klFun.comp
            (ENNReal.measurable_toReal.comp (measurable_arm_rnDeriv nu nu')))
      rw [Measure.lintegral_compProd hmeas]
      apply lintegral_congr
      intro i
      rw [Kernel.sectR_apply]
      simp only [Kernel.comap_apply, banditRewardKernel]
      change (∫⁻ x, ENNReal.ofReal
          (klFun (((nu.P i).rnDeriv (nu'.P i) x).toReal)) ∂nu'.P i) = _
      rw [klDiv_eq_lintegral_klFun_of_ac (arm_ac nu nu' hKL i)]
    _ = ∑ i, klDiv (nu.P i) (nu'.P i) * (pi.select n h) {i} := by
      exact lintegral_fintype _
    _ = ∑ i, ENNReal.ofReal ((pi.select n h).real {i}) *
        klDiv (nu.P i) (nu'.P i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [ofReal_measureReal, mul_comm]

private theorem stepKernel_eq_withDensity {k n : ℕ}
    (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) :
    banditStepKernel nu pi n =
      (banditStepKernel nu' pi n).withDensity
        (fun (_ : BanditHistory k n) (z : Fin k × ℝ) ↦
          (nu.P z.1).rnDeriv (nu'.P z.1) z.2) := by
  have hf : Measurable (Function.uncurry
      (fun (_ : BanditHistory k n) (z : Fin k × ℝ) ↦
        (nu.P z.1).rnDeriv (nu'.P z.1) z.2)) :=
    (measurable_arm_rnDeriv nu nu').comp measurable_snd
  ext h s hs
  rw [Kernel.withDensity_apply _ hf h]
  exact congrArg (fun m : Measure (Fin k × ℝ) ↦ m s)
    (step_withDensity nu nu' hKL pi h).symm

private theorem banditCompProd_withDensity {k n : ℕ}
    (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) :
    ((banditMeasure nu pi n).compProd (banditStepKernel nu' pi n)).withDensity
        (fun p ↦ (nu.P p.2.1).rnDeriv (nu'.P p.2.1) p.2.2) =
      (banditMeasure nu pi n).compProd (banditStepKernel nu pi n) := by
  let f : BanditHistory k n → Fin k × ℝ → ENNReal :=
    fun _ z ↦ (nu.P z.1).rnDeriv (nu'.P z.1) z.2
  have hf : Measurable (Function.uncurry f) :=
    (measurable_arm_rnDeriv nu nu').comp measurable_snd
  have hstep : banditStepKernel nu pi n =
      (banditStepKernel nu' pi n).withDensity f := by
    simpa [f] using stepKernel_eq_withDensity nu nu' hKL pi
  letI : IsFiniteKernel ((banditStepKernel nu' pi n).withDensity f) := by
    rw [← hstep]
    infer_instance
  change ((banditMeasure nu pi n).compProd (banditStepKernel nu' pi n)).withDensity
      (fun p ↦ f p.1 p.2) =
    (banditMeasure nu pi n).compProd (banditStepKernel nu pi n)
  rw [← Measure.compProd_withDensity hf]
  rw [← hstep]

private theorem rnDeriv_banditCompProd {k n : ℕ}
    (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) :
    ((banditMeasure nu pi n).compProd (banditStepKernel nu pi n)).rnDeriv
        ((banditMeasure nu pi n).compProd (banditStepKernel nu' pi n)) =ᵐ[
      (banditMeasure nu pi n).compProd (banditStepKernel nu' pi n)]
        fun p ↦ (nu.P p.2.1).rnDeriv (nu'.P p.2.1) p.2.2 := by
  rw [← banditCompProd_withDensity nu nu' hKL pi]
  exact Measure.rnDeriv_withDensity _
    ((measurable_arm_rnDeriv nu nu').comp measurable_snd)

private theorem banditCompProd_ac {k n : ℕ}
    (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) :
    (banditMeasure nu pi n).compProd (banditStepKernel nu pi n) ≪
      (banditMeasure nu pi n).compProd (banditStepKernel nu' pi n) := by
  refine Measure.AbsolutelyContinuous.compProd_right ?_
  filter_upwards [] with h
  exact step_ac nu nu' hKL pi h

private theorem klDiv_banditCompProd_eq_lintegral_step {k n : ℕ}
    (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) :
    klDiv
        ((banditMeasure nu pi n).compProd (banditStepKernel nu pi n))
        ((banditMeasure nu pi n).compProd (banditStepKernel nu' pi n)) =
      ∫⁻ h, klDiv (banditStepKernel nu pi n h)
        (banditStepKernel nu' pi n h) ∂banditMeasure nu pi n := by
  rw [klDiv_eq_lintegral_klFun_of_ac (banditCompProd_ac nu nu' hKL pi)]
  calc
    (∫⁻ p, ENNReal.ofReal
        (klFun ((((banditMeasure nu pi n).compProd (banditStepKernel nu pi n)).rnDeriv
          ((banditMeasure nu pi n).compProd (banditStepKernel nu' pi n)) p).toReal))
        ∂(banditMeasure nu pi n).compProd (banditStepKernel nu' pi n)) =
        ∫⁻ p, ENNReal.ofReal
          (klFun (((nu.P p.2.1).rnDeriv (nu'.P p.2.1) p.2.2).toReal))
          ∂(banditMeasure nu pi n).compProd (banditStepKernel nu' pi n) := by
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_banditCompProd nu nu' hKL pi] with p hp
      rw [hp]
    _ = ∫⁻ h, ∫⁻ z, ENNReal.ofReal
          (klFun (((nu.P z.1).rnDeriv (nu'.P z.1) z.2).toReal))
          ∂banditStepKernel nu' pi n h ∂banditMeasure nu pi n := by
      have hmeas : Measurable (fun p : BanditHistory k n × (Fin k × ℝ) ↦
          ENNReal.ofReal
            (klFun (((nu.P p.2.1).rnDeriv (nu'.P p.2.1) p.2.2).toReal))) :=
        ENNReal.measurable_ofReal.comp
          (measurable_klFun.comp
            (ENNReal.measurable_toReal.comp
              ((measurable_arm_rnDeriv nu nu').comp measurable_snd)))
      rw [Measure.lintegral_compProd hmeas]
    _ = ∫⁻ h, klDiv (banditStepKernel nu pi n h)
        (banditStepKernel nu' pi n h) ∂banditMeasure nu pi n := by
      apply lintegral_congr
      intro h
      rw [klDiv_eq_lintegral_klFun_of_ac (step_ac nu nu' hKL pi h)]
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_step nu nu' hKL pi h] with z hz
      rw [hz]

private theorem measurable_selection_probability {k n : ℕ}
    (pi : BanditPolicy k) (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (pi.select n h).real {i}) :=
  (Kernel.measurable_coe (pi.select n) (measurableSet_singleton i)).ennreal_toReal

private theorem integrable_selection_probability {k n : ℕ}
    (nu : StochasticBandit k) (pi : BanditPolicy k) (i : Fin k) :
    Integrable (fun h : BanditHistory k n ↦ (pi.select n h).real {i})
      (banditMeasure nu pi n) := by
  apply Integrable.of_mem_Icc 0 1
  · exact (measurable_selection_probability pi i).aemeasurable
  · filter_upwards [] with h
    constructor
    · positivity
    · calc
        (pi.select n h).real {i} ≤ (pi.select n h).real Set.univ :=
          measureReal_mono (Set.subset_univ _)
        _ = 1 := by simp

private theorem klDiv_banditCompProd_eq_sum_selection_integrals {k n : ℕ}
    (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) :
    klDiv
        ((banditMeasure nu pi n).compProd (banditStepKernel nu pi n))
        ((banditMeasure nu pi n).compProd (banditStepKernel nu' pi n)) =
      ∑ i, ENNReal.ofReal
          (∫ h, (pi.select n h).real {i} ∂banditMeasure nu pi n) *
        klDiv (nu.P i) (nu'.P i) := by
  rw [klDiv_banditCompProd_eq_lintegral_step nu nu' hKL pi]
  calc
    (∫⁻ h, klDiv (banditStepKernel nu pi n h)
        (banditStepKernel nu' pi n h) ∂banditMeasure nu pi n) =
        ∫⁻ h, ∑ i, ENNReal.ofReal ((pi.select n h).real {i}) *
          klDiv (nu.P i) (nu'.P i) ∂banditMeasure nu pi n := by
      apply lintegral_congr
      intro h
      exact klDiv_banditStepKernel_eq_sum nu nu' hKL pi h
    _ = ∑ i, ∫⁻ h, ENNReal.ofReal ((pi.select n h).real {i}) *
          klDiv (nu.P i) (nu'.P i) ∂banditMeasure nu pi n := by
      rw [lintegral_finset_sum]
      intro i _
      exact (ENNReal.measurable_ofReal.comp
        (measurable_selection_probability pi i)).mul_const _
    _ = ∑ i, ENNReal.ofReal
          (∫ h, (pi.select n h).real {i} ∂banditMeasure nu pi n) *
        klDiv (nu.P i) (nu'.P i) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∫⁻ h, ENNReal.ofReal ((pi.select n h).real {i}) *
            klDiv (nu.P i) (nu'.P i) ∂banditMeasure nu pi n) =
            (∫⁻ h, ENNReal.ofReal ((pi.select n h).real {i})
              ∂banditMeasure nu pi n) * klDiv (nu.P i) (nu'.P i) :=
          lintegral_mul_const _ (ENNReal.measurable_ofReal.comp
            (measurable_selection_probability pi i))
        _ = ENNReal.ofReal
            (∫ h, (pi.select n h).real {i} ∂banditMeasure nu pi n) *
              klDiv (nu.P i) (nu'.P i) := by
          rw [ofReal_integral_eq_lintegral_ofReal
            (integrable_selection_probability nu pi i)]
          filter_upwards [] with h
          positivity

private theorem klDiv_map_embedding
    {alpha beta : Type*} {ma : MeasurableSpace alpha} {mb : MeasurableSpace beta}
    {mu eta : Measure alpha} [IsFiniteMeasure mu] [IsFiniteMeasure eta]
    {f : alpha → beta} (hf : MeasurableEmbedding f) :
    klDiv (mu.map f) (eta.map f) = klDiv mu eta := by
  by_cases h_ac : mu ≪ eta
  · rw [klDiv_eq_lintegral_klFun_of_ac (hf.absolutelyContinuous_map h_ac),
      klDiv_eq_lintegral_klFun_of_ac h_ac]
    rw [hf.lintegral_map]
    apply lintegral_congr_ae
    filter_upwards [hf.rnDeriv_map mu eta] with x hx
    rw [hx]
  · rw [klDiv_of_not_ac h_ac, klDiv_of_not_ac]
    intro hmap
    apply h_ac
    intro s hetas
    have hetamap : eta.map f (f '' s) = 0 := by
      rw [hf.map_apply, hf.injective.preimage_image]
      exact hetas
    have hmumap := hmap hetamap
    rw [hf.map_apply, hf.injective.preimage_image] at hmumap
    exact hmumap

private theorem klDiv_banditSnoc_map {k n : ℕ}
    (mu eta : Measure (BanditHistory k n × (Fin k × ℝ)))
    [IsFiniteMeasure mu] [IsFiniteMeasure eta] :
    klDiv
        (mu.map (fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2))
        (eta.map (fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2)) =
      klDiv mu eta := by
  have hemb : MeasurableEmbedding
      (fun p : BanditHistory k n × (Fin k × ℝ) ↦
        Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2) := by
    apply MeasurableEmbedding.of_measurable_inverse
      (g := fun h : BanditHistory k (n + 1) ↦ (Fin.init h, h (Fin.last n)))
      measurable_banditHistorySnoc
    · have hrange : Set.range
          (fun p : BanditHistory k n × (Fin k × ℝ) ↦
            Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2) = Set.univ := by
        apply Set.eq_univ_of_forall
        intro h
        exact ⟨(Fin.init h, h (Fin.last n)), Fin.snoc_init_self (q := h)⟩
      rw [hrange]
      exact MeasurableSet.univ
    · fun_prop
    · intro p
      apply Prod.ext
      · exact Fin.init_snoc
          (α := fun _ : Fin (n + 1) ↦ Fin k × ℝ) (n := n) (p := p.1) (x := p.2)
      · exact Fin.snoc_last
          (α := fun _ : Fin (n + 1) ↦ Fin k × ℝ) (n := n) (p := p.1) (x := p.2)
  exact klDiv_map_embedding hemb

private theorem klDiv_banditMeasure_succ_chainRule {k n : ℕ}
    (nu nu' : StochasticBandit k) (pi : BanditPolicy k) :
    klDiv (banditMeasure nu pi (n + 1)) (banditMeasure nu' pi (n + 1)) =
      klDiv (banditMeasure nu pi n) (banditMeasure nu' pi n) +
        klDiv
          ((banditMeasure nu pi n).compProd (banditStepKernel nu pi n))
          ((banditMeasure nu pi n).compProd (banditStepKernel nu' pi n)) := by
  rw [banditMeasure, banditMeasure]
  rw [klDiv_banditSnoc_map]
  exact InformationTheory.klDiv_compProd_eq_add _ _ _ _

end Slot81DivergenceStepScratch

open MeasureTheory ProbabilityTheory InformationTheory
open BanditAlgorithm

theorem solution {k n : ℕ} (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) :
    klDiv (banditMeasure nu pi (n + 1)) (banditMeasure nu' pi (n + 1)) =
      klDiv (banditMeasure nu pi n) (banditMeasure nu' pi n) +
        ∑ i, ENNReal.ofReal
          (∫ h, (pi.select n h).real {i} ∂banditMeasure nu pi n) *
            klDiv (nu.P i) (nu'.P i) := by
  rw [Slot81DivergenceStepScratch.klDiv_banditMeasure_succ_chainRule]
  congr 1
  exact Slot81DivergenceStepScratch.klDiv_banditCompProd_eq_sum_selection_integrals
    nu nu' hKL pi
