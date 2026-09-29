-- Prove2me | solution 1 for MarkovChainCLT.condExp_coord_add
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T00:08:49.493284+00:00
-- url     : https://prove2.me/submissions/8891f083-9c1c-4870-98f1-60c91948492d

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovIterKernel
import Theorems.Thm_MarkovChainCLT_condExp_next_coord
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 2000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (lam : Measure X) [IsProbabilityMeasure lam]
    (h : X → ℝ) (hh : Measurable h) (B : ℝ) (hB : ∀ x, |h x| ≤ B) (m d : ℕ) :
    (fun ω : ℕ → X => ∫ y, h y ∂(iterKernel P d (ω m)))
      =ᵐ[chainMeasure P lam] (chainMeasure P lam)[fun ω : ℕ → X => h (ω (m + d)) |
        MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) m) inferInstance] := by
  classical
  set ν : Measure (ℕ → X) := chainMeasure P lam with hν
  -- basic facts about the coordinate filtration
  have hfle : ∀ k : ℕ,
      MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) k) inferInstance
        ≤ (inferInstance : MeasurableSpace (ℕ → X)) :=
    fun k => (measurable_frestrictLe k).comap_le
  have hfmono : ∀ i j : ℕ, i ≤ j →
      MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) i) inferInstance
        ≤ MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) j) inferInstance := by
    intro i j hij
    have hcomp : (frestrictLe₂ (π := fun _ : ℕ => X) hij)
          ∘ (frestrictLe (π := fun _ : ℕ => X) j)
        = frestrictLe (π := fun _ : ℕ => X) i := frestrictLe₂_comp_frestrictLe hij
    have h1 : Measurable[MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) j) inferInstance]
        (frestrictLe (π := fun _ : ℕ => X) j) := Measurable.of_comap_le le_rfl
    have h2 : Measurable[MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) j) inferInstance]
        (frestrictLe (π := fun _ : ℕ => X) i) := by
      rw [← hcomp]
      exact (measurable_frestrictLe₂ hij).comp h1
    exact h2.comap_le
  have hcoordF : ∀ (k i : ℕ), i ≤ k → Measurable[MeasurableSpace.comap
      (frestrictLe (π := fun _ : ℕ => X) k) inferInstance] (fun ω : ℕ → X => ω i) := by
    intro k i hi
    have h1 : Measurable[MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) k) inferInstance]
        (frestrictLe (π := fun _ : ℕ => X) k) := Measurable.of_comap_le le_rfl
    have h2 := (measurable_pi_apply (⟨i, Finset.mem_Iic.2 hi⟩ : Finset.Iic k)).comp h1
    exact h2
  -- a bounded observable stays bounded after one step of the kernel
  have hIntBound : ∀ (u : X → ℝ), Measurable u → ∀ M : ℝ, (∀ x, |u x| ≤ M) →
      ∀ (μ : Measure X), IsProbabilityMeasure μ → |∫ z, u z ∂μ| ≤ M := by
    intro u hu M hM μ hμ
    refine le_trans abs_integral_le_integral_abs ?_
    have h1 : Integrable (fun z => |u z|) μ :=
      ⟨(continuous_abs.measurable.comp hu).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := M) (ae_of_all _ (fun z => by simpa using hM z))⟩
    have h2 := integral_mono h1 (integrable_const M) (fun z => hM z)
    simpa using h2
  induction d generalizing h with
  | zero =>
      have hmle : MeasurableSpace.comap
          (frestrictLe (π := fun _ : ℕ => X) m) inferInstance
          ≤ (inferInstance : MeasurableSpace (ℕ → X)) := hfle m
      haveI : IsFiniteMeasure (ν.trim hmle) := isFiniteMeasure_trim hmle
      have hfun : (fun ω : ℕ → X => ∫ y, h y ∂(iterKernel P 0 (ω m)))
          = fun ω : ℕ → X => h (ω (m + 0)) := by
        funext ω
        rw [iterKernel_zero, Kernel.id_apply, integral_dirac' _ _ hh.stronglyMeasurable]
        norm_num
      rw [hfun]
      have hsm : StronglyMeasurable[MeasurableSpace.comap
          (frestrictLe (π := fun _ : ℕ => X) m) inferInstance]
          (fun ω : ℕ → X => h (ω (m + 0))) := by
        have hx := hh.comp (hcoordF m (m + 0) (by omega))
        exact hx.stronglyMeasurable
      have hint : Integrable (fun ω : ℕ → X => h (ω (m + 0))) ν :=
        ⟨(hh.comp (measurable_pi_apply (m + 0))).aestronglyMeasurable,
          HasFiniteIntegral.of_bounded (C := B) (ae_of_all _ (fun ω => by simpa using hB _))⟩
      rw [condExp_of_stronglyMeasurable hmle hsm hint]
  | succ k ih =>
      -- one more step: condition first on the coordinates up to `m + k`
      have hmle : MeasurableSpace.comap
          (frestrictLe (π := fun _ : ℕ => X) m) inferInstance
          ≤ (inferInstance : MeasurableSpace (ℕ → X)) := hfle m
      haveI : IsFiniteMeasure (ν.trim hmle) := isFiniteMeasure_trim hmle
      have hmle2 : MeasurableSpace.comap
          (frestrictLe (π := fun _ : ℕ => X) (m + k)) inferInstance
          ≤ (inferInstance : MeasurableSpace (ℕ → X)) := hfle (m + k)
      haveI : IsFiniteMeasure (ν.trim hmle2) := isFiniteMeasure_trim hmle2
      have hle12 : MeasurableSpace.comap
          (frestrictLe (π := fun _ : ℕ => X) m) inferInstance
          ≤ MeasurableSpace.comap
            (frestrictLe (π := fun _ : ℕ => X) (m + k)) inferInstance :=
        hfmono m (m + k) (by omega)
      set Ph : X → ℝ := fun x => ∫ y, h y ∂(P x) with hPh
      have hPhm : Measurable Ph := (hh.stronglyMeasurable.integral_kernel (κ := P)).measurable
      have hPhB : ∀ x, |Ph x| ≤ B := fun x => hIntBound h hh B hB (P x) inferInstance
      -- the tower property
      have hstep := (condExp_next_coord P lam h hh B hB (m + k)).symm
      have hidx : m + k + 1 = m + (k + 1) := by omega
      have htower : ν[fun ω : ℕ → X => h (ω (m + (k + 1))) | MeasurableSpace.comap
          (frestrictLe (π := fun _ : ℕ => X) m) inferInstance]
          =ᵐ[ν] ν[ν[fun ω : ℕ → X => h (ω (m + (k + 1))) | MeasurableSpace.comap
            (frestrictLe (π := fun _ : ℕ => X) (m + k)) inferInstance] | MeasurableSpace.comap
              (frestrictLe (π := fun _ : ℕ => X) m) inferInstance] :=
        (condExp_condExp_of_le hle12 hmle2).symm
      have hinner : ν[fun ω : ℕ → X => h (ω (m + (k + 1))) | MeasurableSpace.comap
          (frestrictLe (π := fun _ : ℕ => X) (m + k)) inferInstance]
          =ᵐ[ν] fun ω : ℕ → X => Ph (ω (m + k)) := by
        rw [← hidx]
        exact hstep
      have hcongr := condExp_congr_ae (m := MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) m) inferInstance) (μ := ν) hinner
      have hIH := ih Ph hPhm hPhB
      -- rewrite the kernel iterate
      have hker : ∀ x : X, ∫ y, Ph y ∂(iterKernel P k x) = ∫ y, h y ∂(iterKernel P (k + 1) x) := by
        intro x
        haveI : IsMarkovKernel (P ∘ₖ iterKernel P k) := Kernel.IsMarkovKernel.comp _ _
        have hint : Integrable h ((P ∘ₖ iterKernel P k) x) :=
          ⟨hh.aestronglyMeasurable,
            HasFiniteIntegral.of_bounded (C := B)
              (ae_of_all _ (fun y => by simpa using hB y))⟩
        have h1 : ∫ z, h z ∂((P ∘ₖ iterKernel P k) x)
            = ∫ y, (∫ z, h z ∂(P y)) ∂(iterKernel P k x) := Kernel.integral_comp hint
        rw [iterKernel_succ]
        rw [h1, hPh]
      filter_upwards [htower, hcongr, hIH] with ω a b c
      show (fun ω : ℕ → X => ∫ y, h y ∂(iterKernel P (k + 1) (ω m))) ω
        = (ν[fun ω : ℕ → X => h (ω (m + (k + 1))) | MeasurableSpace.comap
            (frestrictLe (π := fun _ : ℕ => X) m) inferInstance]) ω
      rw [a, b, ← c, hker (ω m)]
