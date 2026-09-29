-- Prove2me | solution 1 for Zeta23.Tail.norm_sq_uvec_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:04:16.38599+00:00
-- url     : https://prove2.me/submissions/4b6190a3-6ee6-4891-85b3-97a6b2a8b1e9

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
import Theorems.Thm_Zeta23_Tail_grid_sum_le
import Theorems.Thm_Zeta23_Tail_norm_uvec_le

-- from Zeta23.Tail.Basic
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/Basic.lean — shared elementary definitions for prop:tail (the paper §4.2).
-/

noncomputable section

namespace Zeta23
namespace Tail



lemma distI_of_le {T γ : ℝ} (hT : 0 ≤ T) (h : γ ≤ T) : distI T γ = T - γ := by
  unfold distI
  have h1 : max (T - γ) (γ - 2 * T) = T - γ := max_eq_left (by linarith)
  rw [h1, max_eq_right (by linarith)]

lemma distI_of_ge {T γ : ℝ} (hT : 0 ≤ T) (h : 2 * T ≤ γ) : distI T γ = γ - 2 * T := by
  unfold distI
  have h1 : max (T - γ) (γ - 2 * T) = γ - 2 * T := max_eq_right (by linarith)
  rw [h1, max_eq_right (by linarith)]



lemma sqrt_le_distI_of_InTail {T γ : ℝ} (hT : 0 ≤ T) (h : InTail T γ) :
    Real.sqrt T ≤ distI T γ := by
  have hs := Real.sqrt_nonneg T
  rcases h with h | h
  · rw [distI_of_le hT (by linarith)]; linarith
  · rw [distI_of_ge hT (by linarith)]; linarith





end Tail
end Zeta23
end
end

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


/-- d·h ≤ T  (d = ⌊LT/2π⌋, h = 2π/L) [eq:fk]. -/
lemma d_mul_hgrid_le (hL : 0 < P.L T) (hT : 0 ≤ T) :
    (P.d T : ℝ) * (2 * Real.pi / P.L T) ≤ T := by
  have hπ := Real.pi_pos
  have hfl : (P.d T : ℝ) ≤ P.L T * T / (2 * Real.pi) := Nat.floor_le (by positivity)
  calc (P.d T : ℝ) * (2 * Real.pi / P.L T)
      ≤ (P.L T * T / (2 * Real.pi)) * (2 * Real.pi / P.L T) :=
        mul_le_mul_of_nonneg_right hfl (by positivity)
    _ = T := by field_simp


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

theorem solution (hT : T₀ ≤ T) (hL : 2 ≤ P.L T) {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hdecay : ∀ (r y : ℝ), |y| ≤ 1 / 2 → (r : ℂ) - I * y ≠ 0 →
        ‖P.phiHat T (r - I * y)‖ ≤ Real.exp (P.L T / 4) * C₁ / ‖(r : ℂ) - I * y‖ ^ 2)
    {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (htail : InTail T ρ.im) :
    ∑ k, ‖uvec P T ρ k‖ ^ 2
      ≤ (Real.exp (P.L T / 4) * C₁) ^ 2 * P.L T * ((distI T ρ.im) ^ 3)⁻¹ := by
  have hT' : (300 : ℝ) ≤ T := hT
  have hL0 : 0 < P.L T := by linarith
  set K := Real.exp (P.L T / 4) * C₁ with hK
  have hK0 : 0 ≤ K := by positivity
  have hD : 1 ≤ distI T ρ.im := by
    have h1 := sqrt_le_distI_of_InTail (by linarith) htail
    have h2 : (17 : ℝ) ≤ Real.sqrt T := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
    linarith
  calc ∑ k, ‖uvec P T ρ k‖ ^ 2
      ≤ ∑ k : Fin (P.d T),
          K ^ 2 * (|ρ.im - (T + (k : ℕ) * (2 * Real.pi / P.L T))| ^ 4)⁻¹ := by
        refine sum_le_sum fun k _ => ?_
        have h := norm_uvec_le hL0 (by linarith) hC₁ hdecay hρ htail k
        calc ‖uvec P T ρ k‖ ^ 2
            ≤ (K * (|ρ.im - (T + (k : ℕ) * (2 * Real.pi / P.L T))| ^ 2)⁻¹) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h 2
          _ = _ := by rw [mul_pow, inv_pow, ← pow_mul]
    _ = K ^ 2 * ∑ k ∈ range (P.d T),
          (|ρ.im - (T + (k : ℕ) * (2 * Real.pi / P.L T))| ^ 4)⁻¹ := by
        rw [mul_sum, Fin.sum_univ_eq_sum_range
          (fun k : ℕ => K ^ 2 * (|ρ.im - (T + (k : ℕ) * (2 * Real.pi / P.L T))| ^ 4)⁻¹)]
    _ ≤ K ^ 2 * (P.L T * ((distI T ρ.im) ^ 3)⁻¹) :=
        mul_le_mul_of_nonneg_left
          (grid_sum_le hL (by linarith) (d_mul_hgrid_le hL0 (by linarith)) hD) (sq_nonneg _)
    _ = _ := by ring
