-- Prove2me | solution 1 for Zeta23.Assembly.thmA_abstract_err
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:22:18.004065+00:00
-- url     : https://prove2.me/submissions/43ba8d9a-56d5-4173-8231-8509abb473ed

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
import Theorems.Thm_Zeta23_Assembly_Hfun_lam1_ge
import Theorems.Thm_Zeta23_Assembly_err_isLittleO
import Theorems.Thm_Zeta23_Assembly_eventually_N_ge
import Theorems.Thm_Zeta23_Assembly_eventually_clam_bounds
import Theorems.Thm_Zeta23_Assembly_frobGhat_le
import Theorems.Thm_Zeta23_Assembly_isLittleO_sqrtX_Tl
import Theorems.Thm_Zeta23_Assembly_isLittleO_sqrt_mul_l_Tl
import Theorems.Thm_Zeta23_Assembly_seamA

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

lemma frobSq_eq_sum_norm_sq (A : Matrix n n 𝕜) : frobSq A = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold frobSq
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply, map_sum, RCLike.star_def]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]






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


lemma c₀_pos : 0 < c₀ := by
  have := Real.log_two_gt_d9; unfold c₀; linarith


lemma ell1_eq (T : ℝ) : ell1 T = l T + c₀ := by simp only [ell1, c₀]; ring

lemma ell1_pos {T : ℝ} (hl : 0 < l T) : 0 < ell1 T := by
  rw [ell1_eq]; have := c₀_pos; linarith










end HF

/-! ## Part C.  §6 at fixed `T`: the explicit inequality for Theorem A

All quantities are real numbers attached to one fixed `T` (and fixed `λ`, `ϱ`); every error term is
explicit.  Dictionary (paper ↔ arguments): `N = N(T,2T)`, `NII = N(I′∖I) := N(T−D₀,T) + N(2T,2T+D₀)`,
`N0star = N₀*(T,2T)`, `s12 = s₁ + s₂`, `trGh = tr Ĝ`, `frGh = ‖Ĝ‖_F²`, `trAh = tr Â`,
`frAh = ‖Â‖_F²`, `B` = the prop:tail bound for `|tr Ê|` and `‖Ê‖_F` (`≤ 2θ₀/L`). -/

section FixedT


/-- **§6 proof of Thm A, the "`(H(λ₁) − O(𝓔′_T)) N`" line made explicit.**
With `cλ := 1/λ₁ + λ₁/3` (so `4 − cλ − 2 = H(λ₁)`), if `|tr Ĝ − N| ≤ R₁`
("`tr Ĝ = N + O(√X/a)`") and `‖Ĝ‖_F² ≤ cλ N + R₂` ("`‖Ĝ‖_F² ≤ (1/λ₁+λ₁/3)N(1+O(𝓔′_T))`"), then
`N₀*(T,2T) ≥ H(λ₁) N − [4R₁ + R₂ + 3N(I′∖I) + B(4 + 2√(cλ N + R₂) + B)]`. -/
theorem N0star_lower_H
    {N0star N NII trGh frGh B lam₁ R₁ R₂ : ℝ} (hB : 0 ≤ B)
    (h0 : 4 * trGh - frGh - 2 * N - 3 * NII - B * (4 + 2 * Real.sqrt frGh + B) ≤ N0star)
    (htr : |trGh - N| ≤ R₁) (hfr : frGh ≤ (1 / lam₁ + lam₁ / 3) * N + R₂) :
    Hfun lam₁ * N - (4 * R₁ + R₂ + 3 * NII
        + B * (4 + 2 * Real.sqrt ((1 / lam₁ + lam₁ / 3) * N + R₂) + B)) ≤ N0star := by
  have h1 : N - R₁ ≤ trGh := by have := (abs_le.mp htr).1; linarith
  have h2 : Real.sqrt frGh ≤ Real.sqrt ((1 / lam₁ + lam₁ / 3) * N + R₂) := Real.sqrt_le_sqrt hfr
  have h3 : Hfun lam₁ * N = 4 * N - (1 / lam₁ + lam₁ / 3) * N - 2 * N := by simp only [Hfun]; ring
  nlinarith [h0, h1, h2, h3, hB, mul_le_mul_of_nonneg_left h2 hB]

end FixedT

/-! ## Part D.  Unit conversion `Ĝ ↔ G̃` and the trace inputs
(paper §6, proof of Thm A, first lines: "In the units (eq:hatunits), `tr Ĝ = tr G̃/(aL)` and
`‖Ĝ‖_F² = tr G̃²/(aL)²`. By Proposition prop:trace, `tr Ĝ = N + O(√X/a)` … (note that the taper
constant `a` cancels). By (eq:tr2) … `‖Ĝ‖_F² ≤ … = (1/λ₁ + λ₁/3) N (1 + O(𝓔′_T))`") -/

section Units
open Complex

variable {m : Type*} [Fintype m]

lemma rtrace_smul_ofReal (c : ℝ) (M : Matrix m m ℂ) : rtrace ((c : ℂ) • M) = c * rtrace M := by
  unfold rtrace
  rw [Matrix.trace_smul, smul_eq_mul]
  simp

lemma frobSq_smul_ofReal (c : ℝ) (M : Matrix m m ℂ) :
    frobSq ((c : ℂ) • M) = c ^ 2 * frobSq M := by
  rw [frobSq_eq_sum_norm_sq, frobSq_eq_sum_norm_sq, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  simp [Matrix.smul_apply, mul_pow, sq_abs]

variable (P : Params) (T : ℝ)

omit [Fintype m] in
/-- `G̃ = L⁻¹ • G` with the scalar written as a real cast. -/
lemma tilde_eq (M : Matrix m m ℂ) : P.tilde T M = (((P.L T)⁻¹ : ℝ) : ℂ) • M := by
  simp [Params.tilde]

omit [Fintype m] in
/-- `Ĝ = (aL²)⁻¹ • G` with the scalar written as a real cast [eq:hatunits]. -/
lemma hat_eq (M : Matrix m m ℂ) : P.hat T M = (((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) • M := by
  simp [Params.hat]

omit [Fintype m] in
/-- `Ĝ = (aL)⁻¹ • G̃`: hat units are tilde units divided by `aL` ([eq:hatunits] vs [eq:Gdef]). -/
lemma hat_eq_smul_tilde (M : Matrix m m ℂ) :
    P.hat T M = (((P.a T * P.L T)⁻¹ : ℝ) : ℂ) • P.tilde T M := by
  rw [hat_eq, tilde_eq, smul_smul, ← ofReal_mul]
  congr 1
  push_cast
  ring

/-- "`tr Ĝ = tr G̃ /(aL)`" (paper §6). -/
lemma rtrace_hat (M : Matrix m m ℂ) :
    rtrace (P.hat T M) = (P.a T * P.L T)⁻¹ * rtrace (P.tilde T M) := by
  rw [hat_eq_smul_tilde, rtrace_smul_ofReal]

/-- "`‖Ĝ‖_F² = tr G̃² /(aL)²`" (paper §6), with `tr G̃² = ‖G̃‖_F²`. -/
lemma frobSq_hat (M : Matrix m m ℂ) :
    frobSq (P.hat T M) = ((P.a T * P.L T)⁻¹) ^ 2 * frobSq (P.tilde T M) := by
  rw [hat_eq_smul_tilde, frobSq_smul_ofReal]

/-- The prime-side trace computed entrywise: `rtrace (G̃ᵖʳⁱᵐᵉ) = P.trGtilde T`
(Defs: `trGtilde := L⁻¹ Σ_k G_{kk}`). -/
lemma rtrace_tilde_Gp : rtrace (P.tilde T (P.Gp T)) = P.trGtilde T := by
  rw [tilde_eq, rtrace_smul_ofReal]
  simp [Params.trGtilde, rtrace, Matrix.trace, Params.Gp]

/-- The prime-side Frobenius norm computed entrywise: `frobSq (G̃ᵖʳⁱᵐᵉ) = P.trGtildeSq T`
(Defs: `trGtildeSq := (L⁻¹)² Σ_{k,l} G_{kl}²`). -/
lemma frobSq_tilde_Gp : frobSq (P.tilde T (P.Gp T)) = P.trGtildeSq T := by
  rw [tilde_eq, frobSq_smul_ofReal, frobSq_eq_sum_norm_sq]
  simp [Params.trGtildeSq, Params.Gp, sq_abs]

end Units

section TraceInputs

/-- **"`tr Ĝ = N + O(√X/a)` (note that the taper constant `a` cancels)"** (paper §6 / prop:trace).
From [eq:tr1] first form `|tr G̃ − a L N| ≤ C·L·√X`:
`|tr G̃/(aL) − N| ≤ C √X / a` — the main term is exactly `N`, independent of `a`. -/
theorem trGhat_sub_N_le {a L N trGt C sqX : ℝ} (ha : 0 < a) (hL : 0 < L)
    (h : |trGt - a * L * N| ≤ C * (L * sqX)) :
    |(a * L)⁻¹ * trGt - N| ≤ C * sqX / a := by
  have haL : 0 < a * L := mul_pos ha hL
  have e : (a * L)⁻¹ * trGt - N = (a * L)⁻¹ * (trGt - a * L * N) := by field_simp
  rw [e, abs_mul, abs_of_pos (inv_pos.2 haL), ← div_eq_inv_mul, div_le_iff₀ haL]
  calc |trGt - a * L * N| ≤ C * (L * sqX) := h
    _ = C * sqX / a * (a * L) := by field_simp



end TraceInputs

/-! ## Part E.  The asymptotic wrappers (the only place filters appear)

E1: the explicit error of Parts C–D is `o(N)` given the growth facts;  E2: `o(N)` error ⇒ `ε`-form;
E3: `λ → 1⁻`;  E4: dyadic summation `N₀*(T,2T) ⇒ N₀*(T)` (paper §6, end of proof of Thm A). -/

section Asymptotic
open Filter Asymptotics Topology

/-- E2. An `o(N)` error term yields the `ε`-form. -/
theorem eps_form_of_isLittleO {H₀ : ℝ} {N lower err : ℝ → ℝ}
    (hmain : ∀ᶠ T in atTop, H₀ * N T - err T ≤ lower T)
    (hN : ∀ᶠ T in atTop, 0 ≤ N T) (herr : err =o[atTop] N) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (H₀ - ε) * N T ≤ lower T := by
  intro ε hε
  have h := (herr.def hε).and (hmain.and hN)
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hT₀ T hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h3] at h1
  have : err T ≤ ε * N T := (le_abs_self _).trans h1
  linarith








end Asymptotic

/-! ## Part F.  Instantiation with the concrete objects of `Defs.lean`

F2: growth lemmas for the explicit functions `l, L, X` and for `N(T,2T)` under H-RvM;
F3: `thmA_abstract` — Theorem A at fixed `λ < 1` for an abstract `ZeroConfig`, from the named inputs. -/

section Growth
open Filter Asymptotics Topology Real

/-- `l(T) = log(T/2π) → ∞`. -/
lemma tendsto_l_atTop : Tendsto l atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))

lemma eventually_l_pos : ∀ᶠ T in atTop, 0 < l T := tendsto_l_atTop.eventually_gt_atTop 0


/-- `L = λ l → ∞` for `λ > 0`. -/
lemma tendsto_L_atTop (P : Params) (hlam : 0 < P.lam) : Tendsto P.L atTop atTop :=
  tendsto_l_atTop.const_mul_atTop hlam

/-- `log T = l T + log 2π` for `T > 0`. -/
lemma log_eq_l_add {T : ℝ} (hT : 0 < T) : Real.log T = l T + Real.log (2 * π) := by
  rw [l, Real.log_div hT.ne' (by positivity)]; ring

/-- `log T ≤ 2 l T` eventually. -/
lemma eventually_log_le_two_l : ∀ᶠ T in atTop, Real.log T ≤ 2 * l T := by
  filter_upwards [tendsto_l_atTop.eventually_ge_atTop (Real.log (2 * π)), eventually_gt_atTop 0]
    with T h1 h2
  rw [log_eq_l_add h2]; linarith

lemma eventually_log_nonneg : ∀ᶠ T in atTop, 0 ≤ Real.log T :=
  Real.tendsto_log_atTop.eventually_ge_atTop 0

/-- `T l(T) → ∞`. -/
lemma tendsto_Tl_atTop : Tendsto (fun T => T * l T) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ tendsto_l_atTop



/-- H-RvM ⇒ `N(T,2T) → ∞`. -/
lemma tendsto_N_atTop (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) :
    Tendsto (fun T => (Z.N T (2 * T) : ℝ)) atTop atTop :=
  tendsto_atTop_mono' _ (eventually_N_ge Z hR) (tendsto_Tl_atTop.atTop_div_const (by positivity))

/-- `T l = O(N)` under H-RvM, so `o(T l) ⊆ o(N)`. -/
lemma isLittleO_N_of_isLittleO_Tl (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) {f : ℝ → ℝ}
    (hf : f =o[atTop] fun T => T * l T) : f =o[atTop] fun T => (Z.N T (2 * T) : ℝ) := by
  refine hf.trans_isBigO (IsBigO.of_bound (4 * π) ?_)
  filter_upwards [eventually_N_ge Z hR, eventually_ge_atTop 0, eventually_l_pos] with T h hT hl
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  have := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ 4 * π)
  calc T * l T = 4 * π * (T * l T / (4 * π)) := by field_simp
    _ ≤ 4 * π * (Z.N T (2 * T) : ℝ) := this

/-- `l = o(T l)`. -/
lemma isLittleO_l_Tl : l =o[atTop] fun T => T * l T := by
  refine (isLittleO_iff).2 fun c hc => ?_
  filter_upwards [eventually_ge_atTop c⁻¹, eventually_l_pos, eventually_gt_atTop 0] with T hT hl hT0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hl, abs_of_pos (by positivity)]
  have : 1 ≤ c * T := by
    have := mul_le_mul_of_nonneg_left hT hc.le; rwa [mul_inv_cancel₀ hc.ne'] at this
  nlinarith

/-- `log T = o(T l)`. -/
lemma isLittleO_log_Tl : Real.log =o[atTop] fun T => T * l T := by
  refine IsBigO.trans_isLittleO (IsBigO.of_bound 2 ?_) isLittleO_l_Tl
  filter_upwards [eventually_log_le_two_l, eventually_log_nonneg, eventually_l_pos] with T h h0 hl
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_pos hl]; exact h



lemma tendsto_rpow_halflam_sub_one (P : Params) (hlam1 : P.lam ≤ 1) :
    Tendsto (fun T : ℝ => T ^ (P.lam / 2 - 1)) atTop (𝓝 0) := by
  have : Tendsto (fun T : ℝ => T ^ (-(1 - P.lam / 2))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  simpa [neg_sub] using this


/-- `l · T^{λ/2−1} / L = T^{λ/2−1}/λ → 0` (the size of `θ₀/L`, prop:tail). -/
lemma tendsto_theta_over_L (P : Params) (hlam : 0 < P.lam) (hlam1 : P.lam ≤ 1) :
    Tendsto (fun T => l T * T ^ (P.lam / 2 - 1) / P.L T) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_halflam_sub_one P hlam1
  have h2 : (fun T => l T * T ^ (P.lam / 2 - 1) / P.L T) =ᶠ[atTop]
      fun T => P.lam⁻¹ * T ^ (P.lam / 2 - 1) := by
    filter_upwards [eventually_l_pos] with T hl
    simp only [Params.L]; field_simp
  rw [tendsto_congr' h2]
  simpa using h1.const_mul P.lam⁻¹


/-- `a → 1` from [eq:abdef] `1 − 2w/L ≤ a ≤ 1` and `L → ∞`. -/
lemma tendsto_a_one (P : Params) (hlam : 0 < P.lam)
    (ha : ∀ᶠ T in atTop, 1 - 2 * P.w / P.L T ≤ P.a T ∧ P.a T ≤ 1) :
    Tendsto P.a atTop (𝓝 1) := by
  have hlow : Tendsto (fun T => 1 - 2 * P.w / P.L T) atTop (𝓝 1) := by
    have : Tendsto (fun T => 2 * P.w / P.L T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_L_atTop P hlam)
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    (ha.mono fun T h => h.1) (ha.mono fun T h => h.2)

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




/-- **Seam B — the trace inputs in hat units, for the concrete matrices**, given the H-EF bridge
`Z.Gz P T = P.Gp T` (zero side = prime side, [eq:Gdef] "the two expressions agreeing by
Proposition prop:EF"), [eq:tr1]/[eq:tr2] at height `T` with constants `C₁, C₂`, and [eq:RvM] at `T`
in the form `Tℓ₁/2π ≤ N + R_N`:
`|tr Ĝ − N| ≤ C₁√X/a` (the taper constant cancels in the main term) and
`‖Ĝ‖_F² ≤ cλ N + cλ((K−1)N + K R_N)`, `K = (1 + C₂𝓔_T)/a²`, `cλ = 1/λ₁ + λ₁/3`. -/
theorem seamB (hGzGp : Z.Gz P T = P.Gp T) (ha : 0 < P.a T) (hL : 0 < P.L T) (hℓ₁ : 0 < ell1 T)
    {C₁ C₂ ET RN : ℝ}
    (htr1 : |P.trGtilde T - P.a T * P.L T * (Z.N T (2 * T) : ℝ)| ≤ C₁ * (P.L T * Real.sqrt (P.X T)))
    (hK : 0 ≤ 1 + C₂ * ET)
    (htr2 : P.trGtildeSq T - P.mainTr2 T ≤ C₂ * ET * P.mainTr2 T)
    (hRvM : T * ell1 T / (2 * Real.pi) ≤ (Z.N T (2 * T) : ℝ) + RN) :
    |rtrace (P.hat T (Z.Gz P T)) - (Z.N T (2 * T) : ℝ)| ≤ C₁ * Real.sqrt (P.X T) / P.a T ∧
    frobSq (P.hat T (Z.Gz P T)) ≤ (1 / P.lam1 T + P.lam1 T / 3) * (Z.N T (2 * T) : ℝ)
      + (1 / P.lam1 T + P.lam1 T / 3) * (((1 + C₂ * ET) / P.a T ^ 2 - 1) * (Z.N T (2 * T) : ℝ)
          + (1 + C₂ * ET) / P.a T ^ 2 * RN) := by
  rw [hGzGp, rtrace_hat, frobSq_hat, rtrace_tilde_Gp, frobSq_tilde_Gp]
  refine ⟨trGhat_sub_N_le ha hL htr1, ?_⟩
  have := frobGhat_le (T := T) (trG2 := P.trGtildeSq T) (N := (Z.N T (2 * T) : ℝ)) ha hL hℓ₁ hK
    (by simpa [Params.mainTr2] using htr2) hRvM
  simpa [Params.lam1] using this

end FixedTConcrete

/-! ### F3.  Theorem A at fixed `λ < 1` for an abstract zero configuration

The theorems are proved over an abstract error function `Err` (only: eventually nonnegative and
`→ 0`) in place of the concrete `Params.calE` — the `_err` versions below — so that alternative
prime-side chains (e.g. an MV-free one with an enlarged error) plug in directly; the
`calE` statements are kept as specializations. -/

section Main
open Filter Asymptotics Topology

-- `TracesBoundsE` (abstract error rate) and `TracesBounds.toE` live in Zeta23/TracesBoundsE.lean


/-- little-o from a factor tending to zero. -/
lemma isLittleO_of_tendsto_zero_mul {f g : ℝ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    (fun T => f T * g T) =o[atTop] g := by
  simpa using ((isLittleO_one_iff ℝ).2 hf).mul_isBigO (isBigO_refl g atTop)

/-- `O(1)` from an eventual absolute bound. -/
lemma isBigO_one_of_abs_le {f : ℝ → ℝ} {C : ℝ} (h : ∀ᶠ T in atTop, |f T| ≤ C) :
    f =O[atTop] (fun _ => (1:ℝ)) :=
  IsBigO.of_bound C (by simpa using h)

/-- `O(1) · o(N) = o(N)`. -/
lemma isLittleO_of_bdd_mul {f g N : ℝ → ℝ} (hf : f =O[atTop] (fun _ => (1:ℝ)))
    (hg : g =o[atTop] N) : (fun T => f T * g T) =o[atTop] N := by
  simpa using hf.mul_isLittleO hg



end Main

/-! ### F4.  Theorems B and C at fixed `λ < 1` for an abstract zero configuration
(the paper §6, proofs of thm:B and thm:C: [eq:nplus-lower] + [eq:zeroside2]) -/

section MainBC
open Filter Asymptotics Topology

variable {m : Type*} [Fintype m]













end MainBC

/-! ### F5.  `𝓔_T → 0` (paper [thm:traces]: "`𝓔_T ≪_λ w/L + T^{λ−1} log l` (λ<1), `≪ w/L + log l/l` (λ=1)") -/

section CalE
open Filter Topology Real



end CalE

end Assembly
end Zeta23

end
open Matrix Finset RHLinalg
open scoped ComplexOrder
open Zeta23
open Assembly
open Filter Asymptotics Topology

theorem solution (Z : ZeroConfig) (hRvM : RiemannVonMangoldt Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1) (Err : ℝ → ℝ)
    (hTr : TracesBoundsE P Err P.a P.trGtilde P.trGtildeSq (fun T => (Z.N T (2 * T) : ℝ)))
    (hBlock : ∀ᶠ T in atTop, BlockInputs Z P T)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z P T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz P T = P.Gp T)
    (ha : ∀ᶠ T in atTop, 1 - 2 * P.w / P.L T ≤ P.a T ∧ P.a T ≤ 1)
    (hcalE : Tendsto Err atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (Hfun P.lam - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0star T (2 * T) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, htr2⟩ := hTr.tr2
  obtain ⟨CN, T₃, hRvMmain⟩ := hRvM.main
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  -- the functions of T (abbreviations)
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cl : ℝ → ℝ := fun T => 1 / P.lam1 T + P.lam1 T / 3 with hcl
  set K : ℝ → ℝ := fun T => (1 + C₂ * Err T) / P.a T ^ 2 with hK
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / P.a T with hR₁
  set R₂ : ℝ → ℝ := fun T => cl T * ((K T - 1) * N T + K T * (|CN| * Real.log T)) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (P.a T * P.L T) with hBdef
  set err : ℝ → ℝ := fun T => (4 * R₁ T + R₂ T + 3 * (NII Z T : ℝ)
      + B T * (4 + 2 * Real.sqrt (cl T * N T + R₂ T) + B T)) + 1 / (P.lam * l T) * N T with herr
  -- basic limits
  have hLtop := tendsto_L_atTop P hlam0
  have ha1 := tendsto_a_one P hlam0 ha
  have hapos : ∀ᶠ T in atTop, 1 / 2 ≤ P.a T := by
    filter_upwards [ha, hLtop.eventually_ge_atTop (4 * P.w)] with T h hL4
    have hw := hP.one_le_w
    have hLpos : 0 < P.L T := by linarith
    have : 2 * P.w / P.L T ≤ 1 / 2 := by rw [div_le_iff₀ hLpos]; linarith
    linarith [h.1]
  have hcE0 : Tendsto (fun T => C₂ * Err T) atTop (𝓝 0) := by
    simpa using hcalE.const_mul C₂
  have hKto : Tendsto K atTop (𝓝 1) := by
    have h1 : Tendsto (fun T => 1 + C₂ * Err T) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hcE0
    have h2 : Tendsto (fun T => P.a T ^ 2) atTop (𝓝 1) := by simpa using ha1.pow 2
    simpa [hK, Pi.div_def] using h1.div h2 one_ne_zero
  -- (1) the main inequality, eventually in T
  have hmain : ∀ᶠ T in atTop, Hfun P.lam * N T - err T ≤ (Z.N0star T (2 * T) : ℝ) := by
    filter_upwards [hBlock, hTail, hGzGp, hapos, eventually_ge_atTop T₁,
      eventually_ge_atTop T₂, eventually_ge_atTop T₃, eventually_ge_atTop (0:ℝ), eventually_l_pos,
      eventually_log_nonneg, hcE0.eventually (eventually_gt_nhds (show (-1:ℝ) < 0 by norm_num))]
      with T hB hTl hGG ha2 hT₁ hT₂ hT₃ hT0 hl hlog hcE
    have hapos' : 0 < P.a T := by linarith
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hℓ₁ := ell1_pos hl
    have hKnn : 0 ≤ 1 + C₂ * Err T := by linarith
    have hA := seamA hT0 hB hTl hapos' hLpos
    have htr2' : P.trGtildeSq T - P.mainTr2 T ≤ C₂ * Err T * P.mainTr2 T := by
      have := htr2 T hT₂
      simp only at this
      rw [← mul_assoc] at this
      exact (le_abs_self _).trans this
    have htr1' : |P.trGtilde T - P.a T * P.L T * (Z.N T (2 * T) : ℝ)|
        ≤ C₁ * (P.L T * Real.sqrt (P.X T)) := by
      have := htr1 T hT₁; simpa only using this
    have hRvM' : T * ell1 T / (2 * Real.pi) ≤ N T + |CN| * Real.log T := by
      have h1 := (abs_le.mp (hRvMmain T hT₃)).1
      have h2 : CN * Real.log T ≤ |CN| * Real.log T :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hlog
      have h3 : T / (2 * Real.pi) * ell1 T = T * ell1 T / (2 * Real.pi) := by ring
      simp only [hNdef]; linarith
    have hSB := seamB hGG hapos' hLpos hℓ₁ htr1' hKnn htr2' hRvM'
    -- combine with N0star_lower_H and H(λ₁) ≥ H(λ) − 1/(λ l)
    have hB₀ : 0 ≤ B T := div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have h := N0star_lower_H hB₀ hA hSB.1 hSB.2
    have hH := Hfun_lam1_ge P T hlam0 hl
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hHN : (Hfun P.lam - 1 / (P.lam * l T)) * N T ≤ Hfun (P.lam1 T) * N T :=
      mul_le_mul_of_nonneg_right hH hN0
    simp only [herr, hR₁, hR₂, hBdef, hcl, hK, hNdef] at h hHN ⊢
    linarith
  -- (2) err = o(N)
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z hRvM
  -- R₁ = o(N)
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / P.a T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [hapos] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith))]
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z hRvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact this.congr_left fun T => by simp only [hR₁]; ring
  -- R₂ = o(N)
  have o2 : R₂ =o[atTop] N := by
    have hclO : cl =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 / P.lam + 1 / 3) ?_
      filter_upwards [eventually_clam_bounds P hlam0 hlam1] with T h
      rw [abs_of_nonneg h.1]; exact h.2
    have hK1 : Tendsto (fun T => K T - 1) atTop (𝓝 0) := by simpa using hKto.sub_const 1
    have hKO : K =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2) ?_
      filter_upwards [hKto.eventually (eventually_ge_nhds (show (0:ℝ) < 1 by norm_num)),
        hKto.eventually (eventually_le_nhds (show (1:ℝ) < 2 by norm_num))] with T h1 h2
      rw [abs_of_nonneg h1]; exact h2
    have i1 : (fun T => (K T - 1) * N T) =o[atTop] N := isLittleO_of_tendsto_zero_mul hK1
    have i2 : (fun T => K T * (|CN| * Real.log T)) =o[atTop] N :=
      isLittleO_of_bdd_mul hKO ((isLittleO_N_of_isLittleO_Tl Z hRvM isLittleO_log_Tl).const_mul_left _)
    exact isLittleO_of_bdd_mul hclO (i1.add i2)
  -- N(I′∖I) = o(N)
  have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z hRvM isLittleO_sqrt_mul_l_Tl)
  -- B → 0
  have o4 : Tendsto B atTop (𝓝 0) := by
    have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, hapos, eventually_l_pos] with T hTl ha2 hl
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      exact div_nonneg hTl.theta_nonneg (by positivity)
    · filter_upwards [hTail, hapos, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
        with T hTl ha2 hl hθT hT0
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      have hapos' : 0 < P.a T := by linarith
      have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
        _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (P.a T * P.L T) := by
          have : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
              = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
          rw [this]; gcongr
  -- the bracket and the 1/(λ l) term
  have o5 := err_isLittleO (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ)) (B := B) (cl := cl)
    hNtop o1 o2 o3 o4 (eventually_clam_bounds P hlam0 hlam1)
  have o6 : (fun T => 1 / (P.lam * l T) * N T) =o[atTop] N :=
    isLittleO_of_tendsto_zero_mul (tendsto_const_nhds.div_atTop (tendsto_l_atTop.const_mul_atTop hlam0))
  have herr_o : err =o[atTop] N := o5.add o6
  -- (3) conclude
  exact eps_form_of_isLittleO hmain (Eventually.of_forall fun T => Nat.cast_nonneg _) herr_o
