-- Prove2me | Definitions.Def_Zeta23_PrimeSideTemp
-- name    : Zeta23_PrimeSideTemp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:01:54.220732+00:00
-- url     : https://prove2.me/theorems/0be3cb38-8ef8-48a7-a559-a1204bcd037a
-- title:
--   Statement of the trace bounds of Theorem [thm:traces]
-- statement:
--   This bundle packages the *conclusions* of the paper's Theorem [thm:traces] (the summary of §5: equations [eq:tr1], [eq:tr2], [eq:ratio]) as a `Prop`-valued structure, together with the project's uniform interface for big-$O$ estimates. It is a pure statement file: nothing here is assumed as an axiom.
--
--   **Members.**
--   - `EvBound f g` — the interface shape used for every $O(\cdot)$ in the project: an explicit inequality with named constants,
--   $$\mathrm{EvBound}\,f\,g \;:\Leftrightarrow\; \exists\, C>0,\ \exists\, T_0,\ \forall\, T\ge T_0,\ |f(T)|\le C\,g(T),$$
--   with no filter-style $o(1)$ until the final liminf wrapper.
--   - `Params.mainTr2` — the main term of [eq:tr2] (second form): $(TL/2\pi)\cdot(\ell_1^2+L^2/3)$.
--   - `TracesBounds` — the conclusions of [thm:traces], parametric in four real functions of $T$ (for fixed parameters $P=(\varrho,\lambda,w)$): the taper constant $a:=L^{-1}\int\varphi^2$ of [eq:abdef], the trace $\operatorname{tr}\tilde G$ of the normalised matrix $\tilde G:=G/L$ with $G_{kl}=\int_{\mathbb R}\hat\varphi(\tau-\tau_k)\,\hat\varphi(\tau-\tau_l)\,\nu_X(\tau)\,d\tau$ ([eq:Gdef], second expression), the trace $\operatorname{tr}\tilde G^2=\sum_{k,l<d}\tilde G_{kl}^2$, and the zero count $N(T,2T)$ (zeros with ordinate in $(T,2T]$, with multiplicity) as a real number. Its fields record, in `EvBound` form,
--   $$\operatorname{tr}\tilde G = aL\,N(T,2T)+O(L\sqrt X)=L\,N(T,2T)\,(1+O(\mathcal E_T)),\qquad \operatorname{tr}\tilde G^2=\frac{TL}{2\pi}\Bigl(\ell_1^2+\frac{L^2}{3}\Bigr)(1+O(\mathcal E_T)),$$
--   $$\frac{(\operatorname{tr}\tilde G)^2}{\operatorname{tr}\tilde G^2}=F(\lambda_1)\,N(T,2T)\,(1+O(\mathcal E_T)).$$
--   Only the forms consumed by §6 are recorded, and the constants $C$, $T_0$ may depend on all of $P$ — a weakening of the paper's statement.
--   - `ThmTracesHyp P Z` — the canonical instantiation: [thm:traces] for the prime-side traces `P.trGtilde`, `P.trGtildeSq` of `Defs.lean` and the count $N(T,2T)=Z.N\,T\,(2T)$ of the zero configuration $Z$.
--
--   **Role.** The statement is deliberately about the prime-side expressions, not the zero-side matrix; `Assembly.lean` consumes a proof of `ThmTracesHyp P Z` and bridges the two sides via the explicit-formula hypothesis, while `PrimeSideB.lean` proves `ThmTracesHyp` from the paper's published inputs (`PaperInputs`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideTemp.lean, docstring tag [thm:traces]

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
  Bracketed labels ([prop:cross], [eq:Msplit], …) and section numbers (§5.4, …) refer to that paper.
-/

/-!
# Statement of the trace bounds of Theorem [thm:traces]

This file packages the *conclusions* of the paper's **Theorem [thm:traces]** (the paper §5,
subsection "Summary"; equations **[eq:tr1]**, **[eq:tr2]**, **[eq:ratio]**) as a `Prop`-valued
structure `Zeta23.TracesBounds`, and its instantiation `Zeta23.ThmTracesHyp P Z` on the repository's
definitions, so that `Assembly.lean` can consume it while `PrimeSideA.lean` + `PrimeSideB.lean`
prove it.

* It is **not** a Lean `axiom`.  `PrimeSideB.lean` proves
  `thm_traces : PaperInputs Z P → ThmTracesHyp P Z` from the genuine published inputs
  (H-EF, H-cheb, H-MV, H-Γ, H-RvM of `Hypotheses.lean`); this file is a mere statement file.
* The statement is about the **prime-side expressions**
  `Params.trGtilde`, `Params.trGtildeSq` of `Defs.lean` (built from
  `Gentry k l = ∫ φ̂(τ-τ_k) φ̂(τ-τ_l) ν_X(τ) dτ`, the second expression in [eq:Gdef]), *not* about the
  zero-side matrix `ZeroConfig.Gz`; Assembly bridges the two via H-EF itself, so that this statement genuinely
  exercises H-EF, and proving it from the paper's inputs is exactly §5 of the paper.
* Nothing else lives in this file; the genuine hypotheses are kept separately in
  `Hypotheses.lean`.
-/

noncomputable section

open Real

namespace Zeta23

/-- Explicit big-`O` on a neighbourhood of `+∞` with a positive named constant — the
interface shape used for every `O(·)` (explicit inequality with named constants, no
filter-o(1) until the final liminf wrapper):
`EvBound f g  :↔  ∃ C > 0, ∃ T₀, ∀ T ≥ T₀, |f T| ≤ C * g T`. -/
def EvBound (f g : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → |f T| ≤ C * g T

namespace Params

variable (P : Params) (T : ℝ)

/-- The main term of [eq:tr2] (second form): `(T L / 2π) · (ℓ₁² + L²/3)`. -/
def mainTr2 : ℝ := T * P.L T / (2 * π) * (ell1 T ^ 2 + P.L T ^ 2 / 3)

end Params

/-- # `TracesBounds` — the conclusions of the paper's **[thm:traces]**

Parametric in four real functions of `T` (fixed `P = (ϱ, λ, w)`; §6 takes `w = 1`):
* `aT T`   — the taper constant `a := L⁻¹ ∫ φ²` of [eq:abdef];
* `trG T`  — `tr G̃`,  `G̃ := G/L`, `G_{kl} = ∫_ℝ φ̂(τ−τ_k) φ̂(τ−τ_l) ν_X(τ) dτ` ([eq:Gdef], 2nd expression);
* `trG2 T` — `tr G̃² = Σ_{k,l<d} G̃_{kl}²`;
* `Ncnt T` — `N(T,2T)` (zeros with ordinate in `(T,2T]`, with multiplicity), as a real number.
The canonical instantiation is `ThmTracesHyp` below; the parametric form exists so that
`PrimeSideB` can prove it once over abstract data.

Paper statement (the paper, Theorem [thm:traces], verbatim up to TeX):
"Let 0<λ≤1, L=λl, X=e^L, 1≤w≤L/8, and let G̃ be the matrix (eq:Gdef). Put
 𝓔_T := w/L + (l²+X) log l/(T l) + T^{λ/2−1} … Then for T ≥ T₀(λ), with implied constants
 depending only on ϱ,
   tr G̃  = aL N(T,2T) + O(L√X) = L N(T,2T)(1+O(𝓔_T)),                                   (eq:tr1)
   tr G̃² = 2πbL∫_T^{2T}μ² + (T/π)Σ_{n≤X} Λ(n)²/n g(log n) + O(L l log l (l²+X))
         = (TL/2π)(ℓ₁² + L²/3)(1+O(𝓔_T)),                                                 (eq:tr2)
   (tr G̃)²/tr G̃² = F(λ₁) N(T,2T) (1+O(𝓔_T)),   λ₁ = L/ℓ₁ = λ(1 − (2log2−1)/ℓ₁).          (eq:ratio)"

Formalization notes (deviations — all weakenings of the paper's conclusion, and no harder to
consume at fixed λ):
* each `O(·)` is an `EvBound`: `∃ C > 0, ∃ T₀, ∀ T ≥ T₀, |lhs − main| ≤ C · err`; the paper has `C`
  depending only on `ϱ` and `T₀` on `λ` — here both may depend on all of `P = (ϱ, λ, w)`;
* only the second forms of [eq:tr1] (both equalities given) and of [eq:tr2] are recorded — they are
  what §6 uses; the first form of [eq:tr2] is an intermediate result proved in `PrimeSideB`. -/
structure TracesBounds (P : Params) (aT trG trG2 Ncnt : ℝ → ℝ) : Prop where
  /-- [eq:tr1], first equality: `tr G̃ = a L N(T,2T) + O(L √X)`. -/
  tr1 : EvBound (fun T => trG T - aT T * P.L T * Ncnt T) (fun T => P.L T * Real.sqrt (P.X T))
  /-- [eq:tr1], second equality: `tr G̃ = L N(T,2T) (1 + O(𝓔_T))`. -/
  tr1' : EvBound (fun T => trG T - P.L T * Ncnt T) (fun T => P.calE T * (P.L T * Ncnt T))
  /-- [eq:tr2], second form: `tr G̃² = (T L/2π)(ℓ₁² + L²/3)(1 + O(𝓔_T))`. -/
  tr2 : EvBound (fun T => trG2 T - P.mainTr2 T) (fun T => P.calE T * P.mainTr2 T)
  /-- [eq:ratio]: `(tr G̃)² / tr G̃² = F(λ₁) N(T,2T) (1 + O(𝓔_T))` with `λ₁ = L/ℓ₁` (not `λ`). -/
  ratio : EvBound (fun T => trG T ^ 2 / trG2 T - Ffun (P.lam1 T) * Ncnt T)
    (fun T => P.calE T * (Ffun (P.lam1 T) * Ncnt T))

/-- Canonical instantiation of `TracesBounds`:
`ThmTracesHyp P Z` := [thm:traces] for the prime-side traces `P.trGtilde`, `P.trGtildeSq` of
`Defs.lean` ([eq:Gdef] 2nd expression) and the count `N(T,2T) = Z.N T (2T)` of the
zero configuration `Z`.  `Assembly` consumes `(hTr : ThmTracesHyp P Z)`; `PrimeSideB` proves it
from `PaperInputs`. -/
def ThmTracesHyp (P : Params) (Z : ZeroConfig) : Prop :=
  TracesBounds P P.a P.trGtilde P.trGtildeSq (fun T => (Z.N T (2 * T) : ℝ))

end Zeta23

end


