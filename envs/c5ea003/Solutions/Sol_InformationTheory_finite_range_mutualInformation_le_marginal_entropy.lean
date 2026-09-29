-- Prove2me | solution 1 for InformationTheory.finite_range_mutualInformation_le_marginal_entropy
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T00:32:04.813519+00:00
-- url     : https://prove2.me/submissions/fe2fbb1d-4274-45c6-8cdc-2d1209fc24ef

import Theorems.Thm_InformationTheory_compProd_categorical_kl_le_marginal_entropy_general
import Mathlib.Probability.Kernel.Posterior

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal BigOperators ProbabilityTheory

namespace InformationTheory

theorem _root_.solution
    {Omega Alpha : Type} {mOmega : MeasurableSpace Omega}
    {mAlpha : MeasurableSpace Alpha} {k : ℕ}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (f : Omega → Alpha) (g : Omega → Fin k)
    (hf : Measurable f) (hg : Measurable g) :
    (klDiv (Measure.map (fun x ↦ (f x, g x)) mu)
      ((Measure.map f mu).prod (Measure.map g mu))).toReal ≤
      ∑ a, Real.negMulLog ((Measure.map g mu).real {a}) := by
  by_cases hk : k = 0
  · subst k
    exact (g (Classical.choice (nonempty_of_isProbabilityMeasure mu))).elim0
  letI : NeZero k := ⟨hk⟩
  let rho : Measure (Alpha × Fin k) := Measure.map (fun x ↦ (f x, g x)) mu
  let muF : Measure Alpha := Measure.map f mu
  let kappa : Kernel Alpha (Fin k) := rho.condKernel
  letI : IsProbabilityMeasure rho := by
    dsimp [rho]
    exact Measure.isProbabilityMeasure_map (hf.prod hg).aemeasurable
  letI : IsProbabilityMeasure muF := by
    dsimp [muF]
    exact Measure.isProbabilityMeasure_map hf.aemeasurable
  letI : IsMarkovKernel kappa := by
    dsimp [kappa]
    infer_instance
  have hfst : rho.fst = muF := by
    dsimp [rho, muF]
    exact Measure.fst_map_prodMk hg
  have hrho : muF ⊗ₘ kappa = rho := by
    rw [← hfst]
    exact rho.disintegrate rho.condKernel
  have hmarg : kappa ∘ₘ muF = Measure.map g mu := by
    calc
      kappa ∘ₘ muF = (muF ⊗ₘ kappa).snd := by
        rw [Measure.snd_compProd]
      _ = rho.snd := by rw [hrho]
      _ = Measure.map g mu := by
        dsimp [rho]
        exact Measure.snd_map_prodMk hf
  have hbound := compProd_categorical_kl_le_marginal_entropy_general muF kappa
  rw [hrho, hmarg] at hbound
  simpa [rho, muF, Measure.compProd_const] using hbound

end InformationTheory
