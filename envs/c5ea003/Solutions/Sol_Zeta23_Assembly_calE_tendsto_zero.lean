-- Prove2me | solution 1 for Zeta23.Assembly.calE_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:33:46.439209+00:00
-- url     : https://prove2.me/submissions/815a925a-9070-477a-9c5e-1a2c8450013e

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Assembly
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_PrimeSideTemp
import Definitions.Def_Zeta23_TracesBoundsE

-- from Zeta23.Assembly
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

/-!
# §4 "The counting inequalities" and §6 "Proofs of Theorems A, B, C" — assembly

Reference: the paper, labels `prop:zeroside-rank`, `eq:zeroside-rank`,
`prop:zeroside`, `eq:zeroside`, `eq:zeroside2`, and `sec:proofs` (proofs of `thm:A`, `thm:B`, `thm:C`).

Design:
* Parts A–E of this file are **ζ-free and Defs-free**: theorems about Hermitian matrices
  (Part A, consuming the `RHLinalg` §3 lemmas) and about real numbers / explicit real
  functions (Parts B–E).  Every analytic or combinatorial input produced elsewhere
  (prop:block — `ZeroSide.lean`; prop:tail — `Tail.lean`; thm:traces — `PrimeSideTemp.lean`'s
  `TracesBounds`; Riemann–von Mangoldt and the local count — `Hypotheses.lean`; taper facts —
  `Taper.lean`) enters as an explicit, named hypothesis whose docstring quotes the paper label.
* Part F instantiates A–E with the concrete objects of `Defs.lean`: `thmA_abstract`, `thmB_abstract`,
  `thmC_abstract` (Theorems A–C at fixed `λ < 1` for an abstract `ZeroConfig`, taking prop:block / prop:tail /
  the H-EF bridge / [eq:abdef] / thm:traces as named inputs).
* Error terms are explicit inequalities with named constants throughout Parts A–D; filters /
  `Tendsto` appear only in the final `ε`-wrappers (Part E).

## Units (paper §4, [eq:AE], [eq:hatunits])

Three normalisations of the same real-symmetric `d × d` matrix occur:
* `G` [eq:Gdef];
* `G̃ = G / L`, `Ã = A / L`, `Ẽ = E / L` ("tilde units") — lem:weyl and lem:CS are applied to
  `G̃ = Ã + Ẽ` with threshold `θ = θ₀ ≥ ‖Ẽ‖` (prop:zeroside);
* `Ĝ = G / (a L²)`, `Â`, `Ê` ("hat units", [eq:hatunits]) — lem:ranktrace is applied to `Â = P + Q`
  **only** in these units (paper, after prop:zeroside-rank: "Lemma lem:ranktrace is not
  scale-invariant: it must be applied in the units (eq:hatunits), in which tr P ≤ N_on(I′)").
The two systems meet only through the explicit conversion of Part D,
`tr Ĝ = tr G̃ /(aL)`, `‖Ĝ‖_F² = tr G̃² /(aL)²` (paper §6, first line of the proof of Thm A), and the
taper constant `a` must cancel in `tr Ĝ = N + O(√X / a)`.

Scalar field: `ZeroSide.lean` works over `ℂ` (the inertia argument lives on `ℂ^d`); Part A is kept
`RCLike`-generic like `RHLinalg` and is instantiated at `ℂ` in Part F.
-/

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder

namespace Zeta23
namespace Assembly

/-! ## Part A.  Matrix-level counting inequalities (paper §4, "The counting inequalities") -/

section MatrixLevel

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]



end MatrixLevel

/-! ### Frobenius-norm bookkeeping

`RHLinalg.frobSq A = Re tr(Aᴴ A)`.  We identify it with the square of Mathlib's (scoped) Frobenius
norm, to get the triangle inequality `‖Ĝ − Ê‖_F ≤ ‖Ĝ‖_F + ‖Ê‖_F` used in prop:zeroside-rank. -/

section Frob
open scoped Matrix.Norms.Frobenius

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n]







end Frob

section MatrixLevel2

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]




end MatrixLevel2

/-! ## Part B.  The functions `H`, `F` and the `λ₁` versus `λ` step (paper [eq:Fdef], §6)

Vocabulary from `Zeta23/Defs.lean`: `l T = log(T/2π)`, `ell1 T = l T + 2 log 2 − 1`, `Hfun`, `Ffun`,
`P.L T = P.lam * l T`, `P.lam1 T = P.L T / ell1 T`. -/

section HF
open Real















end HF

/-! ## Part C.  §6 at fixed `T`: the explicit inequality for Theorem A

All quantities are real numbers attached to one fixed `T` (and fixed `λ`, `ϱ`); every error term is
explicit.  Dictionary (paper ↔ arguments): `N = N(T,2T)`, `NII = N(I′∖I) := N(T−D₀,T) + N(2T,2T+D₀)`,
`N0star = N₀*(T,2T)`, `s12 = s₁ + s₂`, `trGh = tr Ĝ`, `frGh = ‖Ĝ‖_F²`, `trAh = tr Â`,
`frAh = ‖Â‖_F²`, `B` = the prop:tail bound for `|tr Ê|` and `‖Ê‖_F` (`≤ 2θ₀/L`). -/

section FixedT



end FixedT

/-! ## Part D.  Unit conversion `Ĝ ↔ G̃` and the trace inputs
(paper §6, proof of Thm A, first lines: "In the units (eq:hatunits), `tr Ĝ = tr G̃/(aL)` and
`‖Ĝ‖_F² = tr G̃²/(aL)²`. By Proposition prop:trace, `tr Ĝ = N + O(√X/a)` … (note that the taper
constant `a` cancels). By (eq:tr2) … `‖Ĝ‖_F² ≤ … = (1/λ₁ + λ₁/3) N (1 + O(𝓔′_T))`") -/

section Units
open Complex

variable {m : Type*} [Fintype m]



variable (P : Params) (T : ℝ)








end Units

section TraceInputs




end TraceInputs

/-! ## Part E.  The asymptotic wrappers (the only place filters appear)

E1: the explicit error of Parts C–D is `o(N)` given the growth facts;  E2: `o(N)` error ⇒ `ε`-form;
E3: `λ → 1⁻`;  E4: dyadic summation `N₀*(T,2T) ⇒ N₀*(T)` (paper §6, end of proof of Thm A). -/

section Asymptotic
open Filter Asymptotics Topology









end Asymptotic

/-! ## Part F.  Instantiation with the concrete objects of `Defs.lean`

F2: growth lemmas for the explicit functions `l, L, X` and for `N(T,2T)` under H-RvM;
F3: `thmA_abstract` — Theorem A at fixed `λ < 1` for an abstract `ZeroConfig`, from the named inputs. -/

section Growth
open Filter Asymptotics Topology Real

/-- `l(T) = log(T/2π) → ∞`. -/
lemma tendsto_l_atTop : Tendsto l atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))


lemma eventually_one_le_l : ∀ᶠ T in atTop, 1 ≤ l T := tendsto_l_atTop.eventually_ge_atTop 1

/-- `L = λ l → ∞` for `λ > 0`. -/
lemma tendsto_L_atTop (P : Params) (hlam : 0 < P.lam) : Tendsto P.L atTop atTop :=
  tendsto_l_atTop.const_mul_atTop hlam

/-- `log T = l T + log 2π` for `T > 0`. -/
lemma log_eq_l_add {T : ℝ} (hT : 0 < T) : Real.log T = l T + Real.log (2 * π) := by
  rw [l, Real.log_div hT.ne' (by positivity)]; ring












lemma tendsto_rpow_halflam_sub_one (P : Params) (hlam1 : P.lam ≤ 1) :
    Tendsto (fun T : ℝ => T ^ (P.lam / 2 - 1)) atTop (𝓝 0) := by
  have : Tendsto (fun T : ℝ => T ^ (-(1 - P.lam / 2))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  simpa [neg_sub] using this





end Growth

/-! ### F0.  Window bookkeeping for an abstract `ZeroConfig` (interval additivity; the four
"set-level" facts of prop:zeroside-rank / prop:zeroside:
`s₁+s₂ ≤ N₀*(T,2T) + N(I′∖I)`, `s₁ ≤ N₀ˢ(T,2T) + N(I′∖I)`, `#𝒵(I′) ≤ N_d(T,2T) + N(I′∖I)`,
`N(I′) = N(T,2T) + N(I′∖I)`, where `N(I′∖I) := N(T−D₀,T) + N(2T,2T+D₀)`). -/

section Windows
open Set

variable (Z : ZeroConfig)









variable (T : ℝ)


variable {T}






end Windows

/-! ### F1.  Fixed-`T` assembly with the concrete matrices `Ĝ = P.hat T (Z.Gz P T)` etc.

The inputs from prop:block (ZeroSide.lean) and prop:tail (Tail.lean) are packaged as the two
Prop-structures below, whose fields are exactly the statements those files announce; they are
discharged in those files' instantiation sections. -/

section FixedTConcrete

variable (Z : ZeroConfig) (P : Params) (T : ℝ)

-- `BlockInputs`, `TailInputs`, `NII` live in `Zeta23/Assembly/Inputs.lean` (shared with ZeroSide/Tail).

variable {Z P T}





end FixedTConcrete

/-! ### F3.  Theorem A at fixed `λ < 1` for an abstract zero configuration

The theorems are proved over an abstract error function `Err` (only: eventually nonnegative and
`→ 0`) in place of the concrete `Params.calE` — the `_err` versions below — so that alternative
prime-side chains (e.g. an MV-free one with an enlarged error) plug in directly; the
`calE` statements are kept as specializations. -/

section Main
open Filter Asymptotics Topology

-- `TracesBoundsE` (abstract error rate) and `TracesBounds.toE` live in Zeta23/TracesBoundsE.lean







end Main

/-! ### F4.  Theorems B and C at fixed `λ < 1` for an abstract zero configuration
(the paper §6, proofs of thm:B and thm:C: [eq:nplus-lower] + [eq:zeroside2]) -/

section MainBC
open Filter Asymptotics Topology

variable {m : Type*} [Fintype m]






/-- `𝓔_T ≥ 0` eventually (all three summands are nonnegative once `L > 0`, `l ≥ 1`, `T > 0`). -/
lemma eventually_calE_nonneg (P : Params) (hlam : 0 < P.lam) (hw : 0 ≤ P.w) :
    ∀ᶠ T in atTop, 0 ≤ P.calE T := by
  filter_upwards [eventually_one_le_l, eventually_gt_atTop (0:ℝ)] with T hl hT
  have hL : 0 < P.L T := by simp only [Params.L]; nlinarith
  have hlog : 0 ≤ Real.log (l T) := Real.log_nonneg hl
  have hX : 0 < P.X T := Real.exp_pos _
  simp only [Params.calE]
  positivity







end MainBC

/-! ### F5.  `𝓔_T → 0` (paper [thm:traces]: "`𝓔_T ≪_λ w/L + T^{λ−1} log l` (λ<1), `≪ w/L + log l/l` (λ=1)") -/

section CalE
open Filter Topology Real

/-- `X = (T/2π)^λ ≤ T` once `T ≥ 2π` (for `λ ≤ 1`). -/
lemma X_le_T (P : Params) (hlam1 : P.lam ≤ 1) {T : ℝ} (hT : 2 * π ≤ T) : P.X T ≤ T := by
  have hπ : 0 < 2 * π := by positivity
  have hb : 1 ≤ T / (2 * π) := by rwa [le_div_iff₀ hπ, one_mul]
  have hX : P.X T = (T / (2 * π)) ^ P.lam := by
    rw [Params.X, Params.L, l, Real.rpow_def_of_pos (by positivity)]; ring_nf
  rw [hX]
  calc (T / (2 * π)) ^ P.lam ≤ (T / (2 * π)) ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hb hlam1
    _ = T / (2 * π) := Real.rpow_one _
    _ ≤ T := div_le_self (by linarith) (by linarith [Real.pi_gt_three])


end CalE

end Assembly
end Zeta23

end
open Matrix Finset RHLinalg
open scoped ComplexOrder
open Zeta23
open Assembly
open Filter Topology Real

theorem solution (P : Params) (hlam : 0 < P.lam) (hlam1 : P.lam ≤ 1) (hw : 0 ≤ P.w) :
    Tendsto P.calE atTop (𝓝 0) := by
  have h1 : Tendsto (fun T => P.w / P.L T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_L_atTop P hlam)
  have h2 : Tendsto (fun T : ℝ => Real.log T ^ 2 / T) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    simpa using this
  have h3 : Tendsto (fun T => Real.log (l T) / l T) atTop (𝓝 0) := by
    have : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact this.comp tendsto_l_atTop
  have h4 := tendsto_rpow_halflam_sub_one P hlam1
  have hsum : Tendsto (fun T => P.w / P.L T + (Real.log T ^ 2 / T + Real.log (l T) / l T)
      + T ^ (P.lam / 2 - 1)) atTop (𝓝 0) := by
    simpa using (h1.add (h2.add h3)).add h4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (eventually_calE_nonneg P hlam hw) ?_
  filter_upwards [eventually_one_le_l, eventually_ge_atTop (2 * π)] with T hl hT2π
  have hT : 0 < T := lt_of_lt_of_le (by positivity) hT2π
  have hlpos : 0 < l T := by linarith
  have hlogl : 0 ≤ Real.log (l T) := Real.log_nonneg hl
  have hlogl' : Real.log (l T) ≤ l T := by linarith [Real.log_le_sub_one_of_pos hlpos]
  have hllog : l T ≤ Real.log T := by
    rw [log_eq_l_add hT]
    have : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  have hX := X_le_T P hlam1 hT2π
  have hXpos : 0 ≤ P.X T := (Real.exp_pos _).le
  -- the middle term
  have hmid : (l T ^ 2 + P.X T) * Real.log (l T) / (T * l T)
      ≤ Real.log T ^ 2 / T + Real.log (l T) / l T := by
    have e : (l T ^ 2 + P.X T) * Real.log (l T) / (T * l T)
        = l T * Real.log (l T) / T + P.X T * Real.log (l T) / (T * l T) := by
      field_simp
    rw [e]
    gcongr ?_ + ?_
    · -- l log l / T ≤ (log T)²/T
      apply div_le_div_of_nonneg_right _ hT.le
      calc l T * Real.log (l T) ≤ l T * l T := mul_le_mul_of_nonneg_left hlogl' hlpos.le
        _ ≤ Real.log T * Real.log T := mul_le_mul hllog hllog hlpos.le (hlpos.le.trans hllog)
        _ = Real.log T ^ 2 := by ring
    · -- X log l /(T l) ≤ log l / l
      rw [div_le_div_iff₀ (by positivity) hlpos]
      calc P.X T * Real.log (l T) * l T ≤ T * Real.log (l T) * l T := by gcongr
        _ = Real.log (l T) * (T * l T) := by ring
  simp only [Params.calE]
  linarith
