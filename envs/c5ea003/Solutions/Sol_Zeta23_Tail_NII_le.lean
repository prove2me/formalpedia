-- Prove2me | solution 1 for Zeta23.Tail.NII_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:09:11.961551+00:00
-- url     : https://prove2.me/submissions/ce582808-629b-40b0-a51e-2edecf517332

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_Tail
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_Tail_RankOne
import Theorems.Thm_Zeta23_Tail_LocalCount_ofWindowCount
import Theorems.Thm_Zeta23_Tail_boundary_count_le

-- from Zeta23.Tail
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail.lean — Proposition [prop:tail] (the paper §4.2 "The tail"), assembled for the
concrete objects of Zeta23/Defs.lean.

Paper, verbatim: "Proposition [prop:tail]. Let A₀ ≥ 1 be an absolute constant such that
N(t+1)−N(t) ≤ A₀ log(t+3) for all t ≥ 0. Then for T ≥ T₀,
  ‖Ẽ‖ ≤ θ₀ := 4A₀ C₁² X^{1/2} log(4T)/D₀²,   C₁ := ‖φ″‖₁ = 2‖ϱ″‖₁/w,
so that θ₀ ≤ 32A₀‖ϱ″‖₁² l T^{λ/2−1} ≪ l T^{λ/2−1}. Moreover the trace norm satisfies
‖Ê‖₁ ≤ θ₀/(aL) ≤ 2θ₀/L."
Here E := G − A [eq:AE] is the contribution of the zeros with ordinate γ ∉ I' := (T−D₀, 2T+D₀],
D₀ := T^{1/2} [eq:D0] (including all zeros with γ ≤ 0), Ẽ := E/L,
Ê := E/(aL²) [eq:hatunits].

Structure of the proof (sub-files):
* Zeta23/Tail/RankOne.lean — ‖E‖, ‖E‖₁ ≤ ∑ m_ρ ‖u_ρ‖₂² for E = ∑ m_ρ u_ρ u_ρᵀ  [eq:Enormsum];
* Zeta23/Tail/Grid.lean    — ∑_{k<d} |γ−τ_k|⁻⁴ ≤ L·dist(γ,I)⁻³;
* Zeta23/Tail/Count.lean   — ∑_{γ∉I'} m_ρ dist(γ,I)⁻³ ≤ 4A₀ log(4T)/T, and N(I'∖I) ≪ D₀ l;
* this file              — [eq:hfbound] ⇒ ‖u_ρ k‖ ≤ e^{L/4}C₁|γ−τ_k|⁻², summability of the
  zero-side series entrywise, E = (the series over γ ∉ I'), and the two bounds in the exact
  shapes consumed downstream: ∀ i, |λᵢ(Ẽ)| ≤ θ₀ (for RHLinalg.weyl_posIndexAbove_le) and
  traceNorm Ê ≤ θ₀/(aL) (for [prop:zeroside-rank]).

Hypotheses taken (all proved elsewhere in the repository; none are Lean axioms):
* hloc  — PaperInputs.RvM.local (Hypotheses.lean), two-sided unit-window form;
* hdecay — [eq:hfbound] specialised to f = φ, in the exact shape of
  Zeta23.Params.norm_phiHat_sub_I_mul_le (Taper.lean), with C₁ := P.C1 T = ‖φ″‖₁;
* hEt/hEh — Hermitian-ness of Ẽ, Ê (from the ρ ↦ 1−ρ̄ symmetry).
-/

noncomputable section

open Matrix Finset Complex
open scoped ComplexOrder

namespace Zeta23
namespace Tail

open RHLinalg

/-! ### θ₀ and its size -/





/-! ### The local count from PaperInputs.RvM.local -/


/-! ### The vectors u_ρ and their decay from [eq:hfbound] -/

section Concrete

variable (Z : ZeroConfig) (P : Params) (T : ℝ)




variable {P T}




variable {Z}



end Concrete

/-! ### Summability of the zero-side series and E as the series over γ ∉ I' -/

section Series

variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}



namespace TailHyp

variable (H : TailHyp Z P T A₀ C₁)
include H













end TailHyp

/-! ### Proposition [prop:tail] -/


end Series

/-! ### E is Hermitian (real symmetric) — "since ρ and 1−ρ̄ have the same ordinate, both index
sets are invariant under ρ ↦ 1−ρ̄, so A and E are real symmetric" [eq:AE] -/

section Hermitian




variable {P : Params} {T : ℝ}


variable {Z : ZeroConfig} {A₀ C₁ : ℝ}





end Hermitian

/-! ### Exports in the shapes consumed by Zeta23/Assembly.lean (Assembly.TailInputs) -/

section Export

open Filter

variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}







end Export

end Tail
end Zeta23
end
open Matrix Finset Complex
open scoped ComplexOrder
open Zeta23
open Tail
open RHLinalg
open Filter
variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}

theorem solution (Z : ZeroConfig) {A₀ T : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (hT : T₀ ≤ T) :
    (Assembly.NII Z T : ℝ) ≤ 3 * A₀ * Real.sqrt T * Real.log (4 * T) := by
  classical
  have hT' : (300:ℝ) ≤ T := hT
  have hLC := LocalCount.ofWindowCount Z hA₀ hloc
  have hfin1 : (Z.window (T - D0 T) T).Finite := Z.finite_window _ _
  have hfin2 : (Z.window (2 * T) (2 * T + D0 T)).Finite := Z.finite_window _ _
  set s1 : Finset Z.carrier := hfin1.toFinset.subtype (· ∈ Z.carrier) with hs1
  set s2 : Finset Z.carrier := hfin2.toFinset.subtype (· ∈ Z.carrier) with hs2
  have hN1 : (Z.N (T - D0 T) T : ℝ) = ∑ ρ ∈ s1, (Z.mult (ρ : ℂ) : ℝ) := by
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin1, hs1,
      Finset.sum_subtype_of_mem (f := fun ρ : ℂ => (Z.mult ρ : ℝ))]
    · push_cast; rfl
    · intro x hx; exact ((Set.Finite.mem_toFinset _).mp hx).1
  have hN2 : (Z.N (2 * T) (2 * T + D0 T) : ℝ) = ∑ ρ ∈ s2, (Z.mult (ρ : ℂ) : ℝ) := by
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin2, hs2,
      Finset.sum_subtype_of_mem (f := fun ρ : ℂ => (Z.mult ρ : ℝ))]
    · push_cast; rfl
    · intro x hx; exact ((Set.Finite.mem_toFinset _).mp hx).1
  have hmem1 : ∀ ρ ∈ s1, T - Real.sqrt T < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T := by
    intro ρ hρ
    rw [hs1, Finset.mem_subtype, Set.Finite.mem_toFinset] at hρ
    exact hρ.2
  have hmem2 : ∀ ρ ∈ s2, 2 * T < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T + Real.sqrt T := by
    intro ρ hρ
    rw [hs2, Finset.mem_subtype, Set.Finite.mem_toFinset] at hρ
    exact hρ.2
  have hdisj : Disjoint s1 s2 := by
    rw [Finset.disjoint_left]
    intro ρ h1 h2
    have := (hmem1 ρ h1).2; have := (hmem2 ρ h2).1; linarith
  have hunion : ∀ ρ ∈ s1 ∪ s2, (T - Real.sqrt T < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T)
      ∨ (2 * T < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T + Real.sqrt T) := by
    intro ρ hρ
    rcases Finset.mem_union.mp hρ with h | h
    · exact Or.inl (hmem1 ρ h)
    · exact Or.inr (hmem2 ρ h)
  have h := boundary_count_le hLC hT (s1 ∪ s2) hunion
  rw [Finset.sum_union hdisj] at h
  unfold Assembly.NII
  push_cast
  rw [hN1, hN2]
  exact h
