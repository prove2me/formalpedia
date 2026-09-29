-- Prove2me | Definitions.Def_Zeta23_PrimeSideB
-- name    : Zeta23_PrimeSideB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:18:54.692933+00:00
-- url     : https://prove2.me/theorems/e58f911b-1742-40d7-8a50-508add98a2fb
-- title:
--   Abstract data and hypothesis package for the [thm:traces] assembly
-- statement:
--   This bundle defines the interface through which [thm:traces] — the summary trace estimates of the prime side (paper §5, "Summary") — is assembled from the five §5 sub-results and the classical inputs, all taken as hypotheses on abstract real functions of $T$ at fixed parameters $P = (\varrho, \lambda, w)$.
--
--   `PrimeSide.Data P` is a record of fourteen real-valued functions of $T$, each documented with its paper object: the taper moments $a = L^{-1}\int\varphi^2$ and $b = L^{-1}\int\varphi^4$ [eq:abdef]; the traces $\operatorname{tr}\tilde G$ and $\operatorname{tr}\tilde G^2$; the zero count $N(T, 2T)$; the total form $\mathcal{M} = \iint_{I\times I}\Phi(\tau-\tau')^2 \nu_X(\tau)\nu_X(\tau')$; the six bilinear pieces $\mathcal{M}[\mu,\mu]$, $\mathcal{M}[P_X,P_X]$, $\mathcal{M}[\mu,P_X]$, $\mathcal{M}[\mu,\Pi_X]$, $\mathcal{M}[P_X,\Pi_X]$, $\mathcal{M}[\Pi_X,\Pi_X]$; the integral $\int_T^{2T}\mu^2$; and the sum $\sum_{n\le X}\Lambda(n)^2/n\; g(\log n)$.
--
--   `PrimeSide.Facts D` is the hypothesis structure on such data: the parameter constraints ($0 < \lambda \le 1$, $1 \le w$), the taper sandwich $1 - 2w/L \le b \le a \le 1$ [eq:abdef], H-RvM ($N(T,2T) = T\ell_1/2\pi + O(l)$), the second [eq:muints] formula ($\int_T^{2T}\mu^2 = (T\ell_1^2/4\pi^2)(1 + O(l^{-2}))$), [prop:trace] ($\operatorname{tr}\tilde G = aLN + O(L\sqrt X)$), [lem:ends] ($\operatorname{tr}\tilde G^2 = \mathcal{M} + O(Ll\log l\,(l^2+X))$), the bilinear expansion [eq:Msplit], [prop:mumu], [prop:PP] with its two-sided sandwich $\tfrac{(L-2w)^3}{6} - O(L^2) \le \sum a_n^2 g(y_n) \le \tfrac{L^3}{6} + O(L^2)$, and the four cross bounds of [prop:cross] — each in the explicit-constant form `EvBound` (eventually in $T$, $|\mathrm{lhs}| \le C\cdot\mathrm{err}$).
--
--   Role: from `Facts D` the module derives `TracesBounds` ([eq:tr1], [eq:tr2], [eq:ratio]), checking the paper's constants $\ell_1^2 + L^2/3$ and $F(\lambda_1)$; `Zeta23/PrimeSideB/Traces.lean` instantiates $D$ with the concrete objects to obtain the `ThmTracesHyp` consumed by the §6 assembly and ultimately Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB.lean, docstring tag [thm:traces]

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_PrimeSideTemp

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of the paper
"More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

/-!
# Prime side, part B: [prop:PP] and the assembly of Theorem [thm:traces]

Paper §5 ("The prime side: magnitude"), subsections "Evaluation of 𝓜" and "Summary".

Contents
* §0 glue between the explicit-constant interface shape `EvBound` and Mathlib's `IsBigO`.
* §1 `Zeta23.PaperParams`: elementary facts about the scalar parameters `l, ℓ₁, L, X, λ₁, 𝓔_T`
  of `Defs.lean` (growth, positivity, `𝓔_T → 0`).  Pure real analysis, no hypotheses.
* §2 `Zeta23.PrimeSide.Facts` / `Zeta23.PrimeSide.tracesBounds_of_facts`: the proof of [thm:traces]
  ([eq:tr1], [eq:tr2], [eq:ratio], second forms) from the five sub-results of §5 + [eq:muints] (H-Γ)
  + [eq:RvM] (H-RvM) + [eq:abdef] (Taper), all taken as hypotheses on abstract real functions of `T`.
  This is where the paper's constants `ℓ₁² + L²/3` and `F(λ₁)` are checked.
* §3 [prop:PP]: `𝓜[P_X,P_X] = (T/π) Σ_{n≤X} Λ(n)²/n · g(log n) + O(L² X)` and the sandwich
  `(L−2w)³/6 + O(L²) ≤ Σ a_n² g(y_n) ≤ L³/6 + O(L²)` — over the concrete definitions of `Defs.lean`
  and `Mform`.
-/

noncomputable section

open Real Filter Asymptotics Topology

namespace Zeta23

/-! ## §0.  Explicit-constant ↔ `IsBigO` glue -/

namespace EvBound














end EvBound

/-! ## §1.  The scalar parameters of `Defs.lean` -/

namespace PaperParams






variable (P : Params)
















variable {P}







end PaperParams

/-! ## §2.  Assembly of Theorem [thm:traces] from the §5 sub-results

All quantities are real functions of `T` at fixed `P = (ϱ, λ, w)`.  The hypotheses below are exactly
the conclusions of [prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:PP], [prop:cross]
(the paper §5), [eq:muints] (from H-Γ), [eq:RvM] (H-RvM) and [eq:abdef] (Taper), each in the
explicit-constant form `EvBound`. -/

namespace PrimeSide

open PaperParams

/-- The real-valued functions of `T` entering [thm:traces].  Docstrings give the paper object. -/
structure Data (P : Params) where
  /-- `a := L⁻¹ ∫ φ²` [eq:abdef] -/
  aT : ℝ → ℝ
  /-- `b := L⁻¹ ∫ φ⁴` [eq:abdef] -/
  bT : ℝ → ℝ
  /-- `tr G̃` (prime-side expression, [eq:Gdef] second form, divided by `L`) -/
  trG : ℝ → ℝ
  /-- `tr G̃² = Σ_{k,l<d} G̃_{kl}²` -/
  trG2 : ℝ → ℝ
  /-- `N(T,2T)` -/
  Ncnt : ℝ → ℝ
  /-- `𝓜 := ∬_{I×I} Φ(τ−τ')² ν_X(τ) ν_X(τ') dτ dτ'` [lem:ends] -/
  Mtot : ℝ → ℝ
  /-- `𝓜[μ,μ]` -/
  Mmumu : ℝ → ℝ
  /-- `𝓜[P_X,P_X]` -/
  MPP : ℝ → ℝ
  /-- `𝓜[μ,P_X]` -/
  MmuP : ℝ → ℝ
  /-- `𝓜[μ,Π_X]` -/
  MmuPi : ℝ → ℝ
  /-- `𝓜[P_X,Π_X]` -/
  MPPi : ℝ → ℝ
  /-- `𝓜[Π_X,Π_X]` -/
  MPiPi : ℝ → ℝ
  /-- `∫_T^{2T} μ(τ)² dτ` -/
  intMu2 : ℝ → ℝ
  /-- `Σ_{n ≤ X} Λ(n)²/n · g(log n) = Σ_n a_n² g(y_n)` -/
  sumL2g : ℝ → ℝ

variable {P : Params} (D : Data P)

/-- Hypotheses of the [thm:traces] assembly = conclusions of the §5 sub-results and of the
classical inputs, on the abstract data `D`.  Paper labels in each field's docstring. -/
structure Facts : Prop where
  lam_pos : 0 < P.lam
  lam_le_one : P.lam ≤ 1
  one_le_w : 1 ≤ P.w
  /-- [eq:abdef]: `1 − 2w/L ≤ b ≤ a ≤ 1` (for `T` large, so that `w ≤ L/8`). -/
  abdef : ∀ᶠ T in atTop, 1 - 2 * P.w / P.L T ≤ D.bT T ∧ D.bT T ≤ D.aT T ∧ D.aT T ≤ 1
  /-- [eq:RvM] (H-RvM): `N(T,2T) = T ℓ₁/2π + O(l)`. -/
  rvm : EvBound (fun T => D.Ncnt T - T * ell1 T / (2 * π)) l
  /-- [eq:muints], second formula (from H-Γ): `∫_T^{2T} μ² = (T ℓ₁²/4π²)(1 + O(l⁻²))`. -/
  muints2 : EvBound (fun T => D.intMu2 T - T * ell1 T ^ 2 / (4 * π ^ 2))
      (fun T => T * ell1 T ^ 2 / (4 * π ^ 2) / l T ^ 2)
  /-- [prop:trace]: `tr G̃ = a L N(T,2T) + O(L √X)`. -/
  prop_trace : EvBound (fun T => D.trG T - D.aT T * P.L T * D.Ncnt T)
      (fun T => P.L T * Real.sqrt (P.X T))
  /-- [lem:ends]: `tr G̃² = 𝓜 + O(L l log l (l² + X))`. -/
  lem_ends : EvBound (fun T => D.trG2 T - D.Mtot T)
      (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T))
  /-- [eq:Msplit]: bilinear expansion of `𝓜 = 𝓜[ν_X, ν_X]`, `ν_X = μ + Π_X + P_X`. -/
  Msplit : ∀ᶠ T in atTop, D.Mtot T =
      D.Mmumu T + D.MPP T + 2 * D.MmuP T + 2 * D.MmuPi T + 2 * D.MPPi T + D.MPiPi T
  /-- [prop:mumu], first form: `𝓜[μ,μ] = 2π b L ∫_T^{2T} μ² + O(l² log L)`. -/
  prop_mumu : EvBound (fun T => D.Mmumu T - 2 * π * D.bT T * P.L T * D.intMu2 T)
      (fun T => l T ^ 2 * Real.log (P.L T))
  /-- [prop:PP] (this file, §3), first form:
    `𝓜[P_X,P_X] = (T/π) Σ_{n≤X} Λ(n)²/n g(log n) + O(L² X)`. -/
  prop_PP : EvBound (fun T => D.MPP T - T / π * D.sumL2g T) (fun T => P.L T ^ 2 * P.X T)
  /-- [prop:PP] (this file, §3), sandwich lower half: `Σ a_n² g(y_n) ≥ (L−2w)³/6 − O(L²)`. -/
  sum_lower : EvBound (fun T => min (D.sumL2g T - (P.L T - 2 * P.w) ^ 3 / 6) 0)
      (fun T => P.L T ^ 2)
  /-- sandwich upper half: `Σ a_n² g(y_n) ≤ L³/6 + O(L²)`. -/
  sum_upper : EvBound (fun T => max (D.sumL2g T - P.L T ^ 3 / 6) 0) (fun T => P.L T ^ 2)
  /-- [prop:cross]: `𝓜[μ,P_X] ≪ l √X`. -/
  cross_muP : EvBound D.MmuP (fun T => l T * Real.sqrt (P.X T))
  /-- [prop:cross]: `𝓜[μ,Π_X] ≪ l L √X`. -/
  cross_muPi : EvBound D.MmuPi (fun T => l T * P.L T * Real.sqrt (P.X T))
  /-- [prop:cross]: `𝓜[P_X,Π_X] ≪ L X`. -/
  cross_PPi : EvBound D.MPPi (fun T => P.L T * P.X T)
  /-- [prop:cross]: `𝓜[Π_X,Π_X] ≪ L X / T`. -/
  cross_PiPi : EvBound D.MPiPi (fun T => P.L T * P.X T / T)

/-! ### The assembly -/

section assembly
variable {D} (h : Facts D)
include h













end assembly

end PrimeSide

/-! ## §3.  [prop:PP]

Statement over `Mform` and `Defs.lean`'s `PX, PhiR, g`,
via the 𝒟 / 𝒪₁ / 𝒪₂ decomposition [eq:MPP]. -/

end Zeta23

end


