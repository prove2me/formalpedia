-- Prove2me | solution 1 for ReweightedNPMLE.exists_regular_iterated_derivative_of_analytic_zero
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:12:42.568514+00:00
-- url     : https://prove2.me/submissions/70be6579-0fb2-495e-8e2e-53c9a23ebe8a

import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.HausdorffDimension

-- Inline helpers preserved from ReweightedNPMLE.AnalyticIncidence.
section
/-!
# Analytic derivative detection for incidence sets

A nontrivial globally real-analytic scalar function has a nonzero derivative
of some finite order at every point. This supplies the minimal derivative
order used to turn possibly singular zero sets into regular level sets.
-/

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped BigOperators Topology ENNReal NNReal

namespace ReweightedNPMLE

theorem exists_iteratedFDeriv_ne_zero_of_analytic_nontrivial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : AnalyticOnNhd ℝ f univ)
    (hnonzero : ∃ y, f y ≠ 0) (x : E) :
    ∃ m : ℕ, iteratedFDeriv ℝ m f x ≠ 0 := by
  by_contra hn
  have hderiv : ∀ m : ℕ, iteratedFDeriv ℝ m f x = 0 := by simpa using hn
  obtain ⟨p, r, hp⟩ := hf x (mem_univ x)
  have hdiag : ∀ (m : ℕ) (u : E), p m (fun _ : Fin m ↦ u) = 0 := by
    intro m u
    have hh := hp.iteratedFDeriv_eq_sum_of_completeSpace (fun _ : Fin m ↦ u)
    rw [hderiv] at hh
    simp only [ContinuousMultilinearMap.zero_apply, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left (by positivity)
  have hgerm : f =ᶠ[𝓝 x] 0 := by
    filter_upwards [Metric.isOpen_eball.mem_nhds (Metric.mem_eball_self hp.r_pos)] with y hy
    have hs := hp.hasSum_sub hy
    have hs₀ : HasSum (fun m : ℕ ↦ p m (fun _ : Fin m ↦ y - x)) 0 := by
      simpa only [hdiag] using (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℝ)) 0)
    exact hs.unique hs₀
  have hall := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ x) hgerm
  obtain ⟨y, hy⟩ := hnonzero
  exact hy (hall (mem_univ y))

theorem continuousMultilinearMap_exists_nonzero_basis_word
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d m : ℕ}
    (b : Module.Basis (Fin d) ℝ E) (L : E [×m]→L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ σ : Fin m → Fin d, L (fun i ↦ b (σ i)) ≠ 0 := by
  by_contra hn
  have hzero : ∀ σ : Fin m → Fin d, L (fun i ↦ b (σ i)) = 0 := by simpa using hn
  have hM : L.toMultilinearMap = (0 : E [×m]→L[ℝ] ℝ).toMultilinearMap :=
    Module.Basis.ext_multilinear (fun _ : Fin m ↦ b) (fun σ ↦ by simpa using hzero σ)
  apply hL
  ext v
  exact congrArg (fun M : MultilinearMap ℝ (fun _ : Fin m ↦ E) ℝ ↦ M v) hM







end ReweightedNPMLE
end

/-!
# Analytic derivative detection for incidence sets

A nontrivial globally real-analytic scalar function has a nonzero derivative
of some finite order at every point. This supplies the minimal derivative
order used to turn possibly singular zero sets into regular level sets.
-/

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped BigOperators Topology ENNReal NNReal

open ReweightedNPMLE
open ReweightedNPMLE in
/-- At an analytic zero, some finite-order coordinate derivative vanishes
while its derivative in another basis coordinate is nonzero. All indexing
choices range over the countable family of finite basis words. -/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    (b : Module.Basis (Fin d) ℝ E) (f : E → ℝ) (hf : AnalyticOnNhd ℝ f univ)
    (hnonzero : ∃ y, f y ≠ 0) (x : E) (hx : f x = 0) :
    ∃ (m : ℕ) (ℓ : Fin d) (σ : Fin m → Fin d),
      iteratedFDeriv ℝ m f x (fun i ↦ b (σ i)) = 0 ∧
      fderiv ℝ (fun y ↦ iteratedFDeriv ℝ m f y (fun i ↦ b (σ i))) x (b ℓ) ≠ 0 := by
  classical
  have hex := exists_iteratedFDeriv_ne_zero_of_analytic_nontrivial f hf hnonzero x
  have hfirst := Nat.find_spec hex
  have hzero : iteratedFDeriv ℝ 0 f x = 0 := by
    ext v
    simp [hx]
  have hpos : 0 < Nat.find hex := by
    by_contra hn
    have heq : Nat.find hex = 0 := by omega
    rw [heq, hzero] at hfirst
    exact hfirst rfl
  let m := Nat.find hex - 1
  have hm : m + 1 = Nat.find hex := by omega
  have hmzero : iteratedFDeriv ℝ m f x = 0 := by
    by_contra hne
    have hle := Nat.find_min' hex hne
    omega
  rw [← hm] at hfirst
  obtain ⟨ρ, hρ⟩ := continuousMultilinearMap_exists_nonzero_basis_word b _ hfirst
  refine ⟨m, ρ 0, fun i ↦ ρ i.succ, ?_, ?_⟩
  · rw [hmzero]
    simp
  · have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ m f) x :=
      ((hf x (mem_univ x)).contDiffAt : ContDiffAt ℝ ⊤ f x).differentiableAt_iteratedFDeriv
        (by simp)
    rw [fderiv_continuousMultilinear_apply_const_apply hdiff]
    simpa only [iteratedFDeriv_succ_apply_left, Fin.tail_def] using hρ
