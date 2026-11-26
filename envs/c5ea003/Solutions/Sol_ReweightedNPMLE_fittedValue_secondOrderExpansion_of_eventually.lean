-- Prove2me | solution 1 for ReweightedNPMLE.fittedValue_secondOrderExpansion_of_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:00:14.940704+00:00
-- url     : https://prove2.me/submissions/746432e1-40e1-4910-8b64-532c18b33b0a

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Hessian structure of the fitted likelihood value

This file turns the envelope identity into the analytic Hessian facts used by
the paper.  The derivative of the fitted log-vector induces the second
derivative of the optimized value.  Mathlib's second-derivative symmetry
theorem makes its matrix Hermitian, while monotonicity of fitted logs makes
its quadratic form nonnegative.  Thus, at every differentiability point, the
matrix representing the fitted-log derivative is positive semidefinite.
-/

open Set Filter Asymptotics
open Matrix
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Local second-order envelope expansion.  Only the gradient identity in a
neighborhood of the base weight is needed, not differentiability at every
weight vector. -/
theorem solution {n : ℕ}
    (psi : (Fin n → ℝ) → ℝ)
    (z : (Fin n → ℝ) → (Fin n → ℝ))
    {w : Fin n → ℝ}
    (hpsi : ∀ᶠ q in nhds w, HasFDerivAt psi (fittedLogLinearFunctional (z q)) q)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt z J w) (h : Fin n → ℝ) :
    (fun t : ℝ ↦ psi (w + t • h) - psi w -
        t * (∑ i, h i * z w i) -
        (t ^ 2 / 2) * (∑ i, h i * J h i)) =o[nhdsWithin 0 (Ioi 0)]
      (fun t : ℝ ↦ t ^ 2) := by
  let path : ℝ → (Fin n → ℝ) := fun t ↦ w + t • h
  let ell : ℝ := ∑ i, h i * z w i
  let H : ℝ := ∑ i, h i * J h i
  let a : ℝ → ℝ := fun t ↦ fittedLogLinearFunctional h (z (path t))
  let f : ℝ → ℝ := fun t ↦ psi (path t) - psi w - t * ell
  let f' : ℝ → ℝ := fun t ↦ a t - ell
  let g : ℝ → ℝ := fun t ↦ t ^ 2
  let g' : ℝ → ℝ := fun t ↦ 2 * t
  have hpath (t : ℝ) : HasDerivAt path h t := by
    simpa [path] using (hasDerivAt_id (x := t)).smul_const h |>.const_add w
  have htend : Tendsto path (nhds 0) (nhds w) := by
    simpa [path] using (hpath 0).continuousAt.tendsto
  have hnear : ∀ᶠ t in nhds (0 : ℝ),
      HasFDerivAt psi (fittedLogLinearFunctional (z (path t))) (path t) :=
    htend.eventually hpsi
  have hff' : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, HasDerivAt f (f' t) t := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hnear] with t ht
    have hc := ht.comp_hasDerivAt t (hpath t)
    have hd := (hc.sub_const (psi w)).sub ((hasDerivAt_id t).mul_const ell)
    simpa [f, f', a, Function.comp_def, fittedLogLinearFunctional_apply,
      mul_comm] using hd
  have hgg' : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, HasDerivAt g (g' t) t := by
    filter_upwards [] with t
    simpa [g, g', id_eq] using (hasDerivAt_id t).pow 2
  have hg' : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, g' t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_ne_zero (by norm_num) ht
  have hfa : Tendsto f (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds 0) := by
    have hpsi0 := hpsi.self_of_nhds
    have hp0 : HasFDerivAt psi (fittedLogLinearFunctional (z w)) (path 0) := by
      simpa [path] using hpsi0
    have hc := (hp0.comp_hasDerivAt 0 (hpath 0)).continuousAt
    have hfcont : ContinuousAt f 0 := by
      exact (hc.sub continuousAt_const).sub (by fun_prop)
    simpa [f, path] using hfcont.tendsto.mono_left nhdsWithin_le_nhds
  have hga : Tendsto g (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds 0) := by
    have hc : ContinuousAt g 0 := by fun_prop
    simpa [g] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hz0 : HasFDerivAt z J (path 0) := by simpa [path] using hz
  have hline : HasDerivAt (fun t ↦ z (path t)) (J h) 0 := by
    simpa [Function.comp_def] using hz0.comp_hasDerivAt 0 (hpath 0)
  have ha : HasDerivAt a H 0 := by
    have hc := (fittedLogLinearFunctional h).hasFDerivAt.comp_hasDerivAt 0 hline
    simpa [a, H, Function.comp_def, fittedLogLinearFunctional_apply, mul_comm] using hc
  have ha0 : a 0 = ell := by
    simp [a, path, ell, fittedLogLinearFunctional_apply, mul_comm]
  have hdiv : Tendsto (fun t ↦ f' t / g' t)
      (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds (H / 2)) := by
    have hs := ha.tendsto_slope_zero.div_const (2 : ℝ)
    apply hs.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht
    dsimp [f', g']
    simp only [zero_add, ha0, smul_eq_mul]
    field_simp [ht0]
  have hlim : Tendsto (fun t ↦ f t / t ^ 2)
      (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds (H / 2)) :=
    HasDerivAt.lhopital_zero_nhdsNE hff' hgg' hg' hfa hga hdiv
  rw [isLittleO_iff_tendsto]
  · have hbase := hlim.mono_left
        (nhdsWithin_mono 0 (show Ioi (0 : ℝ) ⊆ {0}ᶜ by
          intro t ht
          exact ne_of_gt ht))
    have hsub : Tendsto (fun t ↦ f t / t ^ 2 - H / 2)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa using hbase.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ H / 2)
          (nhdsWithin 0 (Ioi 0)) (nhds (H / 2)))
    apply hsub.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    dsimp [f, path, ell, H]
    field_simp [ht0]
  · intro t ht
    have ht0 : t = 0 := sq_eq_zero_iff.mp ht
    subst t
    simp
