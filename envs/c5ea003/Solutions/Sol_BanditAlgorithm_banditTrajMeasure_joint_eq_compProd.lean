-- Prove2me | solution 1 for BanditAlgorithm.banditTrajMeasure_joint_eq_compProd
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T16:56:34.758814+00:00
-- url     : https://prove2.me/submissions/785d1f59-7e34-4843-a613-3fdf060cf917

import Definitions.Def_BanditTrajectory
import Theorems.Thm_ProbabilityTheory_compProd_map_left

/-!
# The one-step joint law of the infinite-horizon canonical bandit model

`P.map (fun ω ↦ (prefix n ω, ω n)) = (P.map (prefix n)) ⊗ₘ banditStepKernel ν π n`

for `P = banditTrajMeasure ν π`: conditionally on the first `n` rounds, round `n + 1` is drawn
from the one-round step kernel. This is the structural fact that lets a divergence computation on
the infinite trajectory space be carried out one round at a time.

Mathlib supplies the corresponding statement for `Kernel.trajMeasure` in its own indexing, where
histories are indexed by an initial segment `Iic a` rather than by `Fin (a + 1)`; the two are
reconciled by `banditIicHistory` together with `ProbabilityTheory.compProd_map_left`.
-/

open MeasureTheory ProbabilityTheory Preorder

namespace BanditAlgorithm

theorem _root_.solution {k : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k) (n : ℕ) :
    (banditTrajMeasure ν π).map (fun ω ↦ (banditTrajPrefix k n ω, ω n))
      = ((banditTrajMeasure ν π).map (banditTrajPrefix k n)) ⊗ₘ (banditStepKernel ν π n) := by
  set P := banditTrajMeasure ν π with hP
  cases n with
  | succ a =>
      -- `banditTrajPrefix k (a+1)` is Mathlib's `frestrictLe a` followed by the reindexing
      have hprefix : banditTrajPrefix k (a + 1)
          = (banditIicHistory k a) ∘ (Preorder.frestrictLe a) := rfl
      have hι : Measurable (banditIicHistory k a) := measurable_banditIicHistory
      have hfr : Measurable (Preorder.frestrictLe (π := fun _ : ℕ ↦ Fin k × ℝ) a) := by fun_prop
      have hmath := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ : ℕ ↦ Fin k × ℝ)
        (μ₀ := banditStepKernel ν π 0 fun t ↦ t.elim0)
        (κ := banditTrajKernel ν π) (a := a)
      calc P.map (fun ω ↦ (banditTrajPrefix k (a + 1) ω, ω (a + 1)))
          = (P.map (fun ω ↦ (Preorder.frestrictLe a ω, ω (a + 1)))).map
              (Prod.map (banditIicHistory k a) id) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
        _ = ((P.map (Preorder.frestrictLe a)) ⊗ₘ (banditTrajKernel ν π a)).map
              (Prod.map (banditIicHistory k a) id) :=
            congrArg (Measure.map (Prod.map (banditIicHistory k a) id)) hmath.symm
        _ = ((P.map (Preorder.frestrictLe a)).map (banditIicHistory k a)) ⊗ₘ
              (banditStepKernel ν π (a + 1)) :=
            (ProbabilityTheory.compProd_map_left _ hι _).symm
        _ = (P.map (banditTrajPrefix k (a + 1))) ⊗ₘ (banditStepKernel ν π (a + 1)) := by
            rw [hprefix, ← Measure.map_map hι hfr]
  | zero =>
      -- the empty prefix carries no information: both sides are the law of round one
      have hcoord : P.map (fun ω ↦ ω 0)
          = banditStepKernel ν π 0 (fun t ↦ t.elim0) := by
        have h1 : P.map (Preorder.frestrictLe (π := fun _ : ℕ ↦ Fin k × ℝ) 0)
            = (banditStepKernel ν π 0 fun t ↦ t.elim0).map
              (MeasurableEquiv.piUnique (fun _i : Finset.Iic (0 : ℕ) ↦ Fin k × ℝ)).symm := by
          rw [hP, banditTrajMeasure, Kernel.trajMeasure,
            Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe,
            Kernel.partialTraj_self, Measure.id_comp]
        have h2 : (fun ω : ℕ → Fin k × ℝ ↦ ω 0)
            = (MeasurableEquiv.piUnique (fun _i : Finset.Iic (0 : ℕ) ↦ Fin k × ℝ)) ∘
              (Preorder.frestrictLe (π := fun _ : ℕ ↦ Fin k × ℝ) 0) := rfl
        rw [h2, ← Measure.map_map (by fun_prop) (by fun_prop), h1,
          Measure.map_map (by fun_prop) (by fun_prop)]
        exact Measure.map_id
      haveI : MeasurableSingletonClass (BanditHistory k 0) :=
        ⟨fun a ↦ by
          convert MeasurableSet.univ using 1
          ext x
          simp [Subsingleton.elim x a]⟩
      have hconst : banditTrajPrefix k 0
          = fun _ : ℕ → Fin k × ℝ ↦ (fun t : Fin 0 ↦ t.elim0) := by
        funext ω; funext t; exact t.elim0
      have hdirac : P.map (banditTrajPrefix k 0)
          = Measure.dirac (fun t : Fin 0 ↦ t.elim0) := by
        rw [hconst, Measure.map_const]
        simp
      ext s hs
      rw [hdirac, Measure.dirac_compProd_apply hs]
      calc (P.map (fun ω ↦ (banditTrajPrefix k 0 ω, ω 0))) s
          = P ((fun ω ↦ (banditTrajPrefix k 0 ω, ω 0)) ⁻¹' s) :=
            Measure.map_apply (by fun_prop) hs
        _ = P ((fun ω ↦ ω 0) ⁻¹' (Prod.mk (fun t : Fin 0 ↦ t.elim0) ⁻¹' s)) := by
            rw [hconst]; rfl
        _ = (P.map (fun ω ↦ ω 0)) (Prod.mk (fun t : Fin 0 ↦ t.elim0) ⁻¹' s) :=
            (Measure.map_apply (by fun_prop) (measurable_prodMk_left hs)).symm
        _ = (banditStepKernel ν π 0 (fun t ↦ t.elim0))
              (Prod.mk (fun t : Fin 0 ↦ t.elim0) ⁻¹' s) := by rw [hcoord]

end BanditAlgorithm
