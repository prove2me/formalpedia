-- Prove2me | solution 1 for Zeta23.Tail.norm_uvec_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:05:11.377098+00:00
-- url     : https://prove2.me/submissions/988a8a2a-b223-428f-bd66-a59bcbde7575

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



lemma gammaOf_sub_ofReal (ρ : ℂ) (x : ℝ) :
    gammaOf ρ - x = ((ρ.im - x : ℝ) : ℂ) - I * ((ρ.re - 1 / 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [gammaOf]

variable {P T}

/-- τ_k = T + k·(2π/L) as a real number, for k : Fin d. -/
lemma tau_fin (k : Fin (P.d T)) : P.tau T k = T + (k : ℕ) * (2 * Real.pi / P.L T) := by
  unfold Params.tau Params.hgrid; push_cast; ring

/-- d·h ≤ T  (d = ⌊LT/2π⌋, h = 2π/L) [eq:fk]. -/
lemma d_mul_hgrid_le (hL : 0 < P.L T) (hT : 0 ≤ T) :
    (P.d T : ℝ) * (2 * Real.pi / P.L T) ≤ T := by
  have hπ := Real.pi_pos
  have hfl : (P.d T : ℝ) ≤ P.L T * T / (2 * Real.pi) := Nat.floor_le (by positivity)
  calc (P.d T : ℝ) * (2 * Real.pi / P.L T)
      ≤ (P.L T * T / (2 * Real.pi)) * (2 * Real.pi / P.L T) :=
        mul_le_mul_of_nonneg_right hfl (by positivity)
    _ = T := by field_simp

/-- "τ_0,…,τ_{d−1} ∈ [T, 2T)" [eq:fk]. -/
lemma tau_mem (hL : 0 < P.L T) (hT : 0 ≤ T) (k : Fin (P.d T)) :
    T ≤ P.tau T k ∧ P.tau T k < 2 * T := by
  rw [tau_fin]
  have hπ := Real.pi_pos
  have hh : 0 < 2 * Real.pi / P.L T := by positivity
  have hk : ((k : ℕ) : ℝ) + 1 ≤ P.d T := by exact_mod_cast k.2
  have hd := d_mul_hgrid_le hL hT
  constructor
  · have : 0 ≤ ((k : ℕ) : ℝ) * (2 * Real.pi / P.L T) := by positivity
    linarith
  · nlinarith

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
variable (Z : ZeroConfig) (P : Params) (T : ℝ)
variable {P T}
variable {Z}

theorem solution (hL : 0 < P.L T) (hT : 0 < T) {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hdecay : ∀ (r y : ℝ), |y| ≤ 1 / 2 → (r : ℂ) - I * y ≠ 0 →
        ‖P.phiHat T (r - I * y)‖ ≤ Real.exp (P.L T / 4) * C₁ / ‖(r : ℂ) - I * y‖ ^ 2)
    {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (htail : InTail T ρ.im) (k : Fin (P.d T)) :
    ‖uvec P T ρ k‖
      ≤ (Real.exp (P.L T / 4) * C₁) * (|ρ.im - (T + (k : ℕ) * (2 * Real.pi / P.L T))| ^ 2)⁻¹ := by
  set r : ℝ := ρ.im - P.tau T k with hr
  set y : ℝ := ρ.re - 1 / 2 with hy
  have hstrip := Z.strip ρ hρ
  have hyab : |y| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hstrip.1, hstrip.2]
  have hτ := tau_mem hL hT.le k
  have hsq : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hr0 : r ≠ 0 := by
    rcases htail with h | h
    · have : r < 0 := by rw [hr]; linarith
      exact this.ne
    · have : 0 < r := by rw [hr]; linarith
      exact this.ne'
  have hz : (r : ℂ) - I * y ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hr0 this
  have hnormz : r ^ 2 ≤ ‖(r : ℂ) - I * y‖ ^ 2 := by
    have h1 : |((r : ℂ) - I * y).re| ≤ ‖(r : ℂ) - I * y‖ := Complex.abs_re_le_norm _
    have h2 : ((r : ℂ) - I * y).re = r := by simp
    rw [h2] at h1
    calc r ^ 2 = |r| ^ 2 := (sq_abs r).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg r) h1 2
  have hrsq : 0 < r ^ 2 := by positivity
  have heq : uvec P T ρ k = P.phiHat T (r - I * y) := by
    unfold uvec; rw [gammaOf_sub_ofReal]
  rw [heq, ← tau_fin, ← hr, sq_abs]
  calc ‖P.phiHat T (r - I * y)‖ ≤ Real.exp (P.L T / 4) * C₁ / ‖(r : ℂ) - I * y‖ ^ 2 :=
        hdecay r y hyab hz
    _ ≤ Real.exp (P.L T / 4) * C₁ / r ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) hrsq hnormz
    _ = _ := by rw [div_eq_mul_inv]
