-- Prove2me | Definitions.Def_Zeta23_PrimeSideB_PPKernel
-- name    : Zeta23_PrimeSideB_PPKernel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:20:00.70967+00:00
-- url     : https://prove2.me/theorems/4cae89a4-a64c-45b1-b2ca-e07290aa4592
-- title:
--   Shear, trigonometric inner integrals $J$, and the moments $C^{\pm}, S^{\pm}$ for [prop:PP]
-- statement:
--   This bundle collects the kernel-level definitions for the evaluation of $\mathcal{M}[P_X, P_X]$ in [prop:PP] (paper §5.4), which reduces the double integral over $I \times I$ ($I = [T, 2T]$) to explicit trigonometric integrals.
--
--   **The shear.** `shearHomeo` is the homeomorphism $(x, \tau') \mapsto (x + \tau', \tau')$ of $\mathbb{R}^2$ (inverse $(\tau, \tau') \mapsto (\tau - \tau', \tau')$), the measure-preserving substitution $\tau = \tau' + x$; `Ix T x` is the resulting $\tau'$-window at offset $x$: $I \cap (I - x) = [\max(T - x, T),\ \min(2T - x, 2T)]$, which is $[T + x^-, 2T - x^+]$ for $|x| < T$ and empty for $|x| > T$.
--
--   **Inner integrals.** `Jker` is the closed form of $J(\theta, c; \alpha, \beta) := \int_\alpha^\beta \cos(\theta t + c)\, dt$: it equals $(\beta - \alpha)\cos c$ when $\theta = 0$ and $[\sin(\theta\beta + c) - \sin(\theta\alpha + c)]/\theta$ otherwise (note the Lean convention $x/0 = 0$ never arises since the cases are split explicitly). `JmK` and `JpK` are the difference- and sum-frequency inner integrals $J(y - y', xy;\ I \cap (I - x))$ and $J(y + y', xy;\ I \cap (I - x))$, and
--   $$A^{\mp}(y, y') := \int_{[-T,T]} \Phi(x)^2\, J^{\mp}(x)\, dx$$
--   (`Aminus`, `Aplus`) are the two halves of $\mathcal{M}[\cos(\cdot\, y), \cos(\cdot\, y')]$ arising from $\cos A \cos B = \tfrac12\cos(A - B) + \tfrac12\cos(A + B)$ [eq:MPP].
--
--   **Moments.** `Cp`, `Sp`, `Cm`, `Sm` are the four half-line trigonometric moments of $\Phi^2$ (the paper's $\alpha_n^{\pm}$, split into real and imaginary parts): $C^{+}(y) = \int_0^T \Phi^2 \cos(xy)$, $S^{+}(y) = \int_0^T \Phi^2 \sin(xy)$, and $C^{-}, S^{-}$ the same over $[-T, 0]$.
--
--   Role: these definitions carry the $\mathcal{D}/\mathcal{O}_1/\mathcal{O}_2$ decomposition of [eq:MPP] — the diagonal terms give the main term $\pi T\, g(y_n)$ via [eq:Phi2FT], the off-diagonal difference-frequency terms are bounded by the Montgomery–Vaughan inequality H-MV applied to eight sums built from $C^{\pm}, S^{\pm}$, and the sum-frequency terms are $O(XL)$ — feeding `Zeta23/PrimeSideB/PP.lean` and thence [thm:traces].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PPKernel.lean, docstring tag [eq:MPP]

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Defs

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
# Kernel lemmas for [prop:PP] (§5.4)

Pure measure-theory / trigonometric-integral / H-MV-application lemmas used by
`Zeta23/PrimeSideB/PP.lean`.

* `sqIntegral_shear`: the substitution `τ = τ' + x` on the square `I×I` (§5.4).
* `intervalIntegral_cos_linear*`: `∫_α^β cos(θt + c) dt` closed forms and the bound `2/|θ|` (§5.4).
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction ComplexConjugate

namespace Zeta23
namespace PrimeSide

/-! ## Elementary facts about the index range `primeRange X = Finset.Ioc 0 ⌊X⌋₊` -/

section Basics











end Basics

/-! ## The shear `(τ,τ') ↦ (x,τ') = (τ−τ',τ')` on `I × I`  (§5.4) -/

section Shear
variable {Φ : ℝ → ℝ} {T : ℝ}

/-- The shear `(x, τ') ↦ (x + τ', τ')` of `ℝ²` as a homeomorphism (its inverse is
`(τ, τ') ↦ (τ − τ', τ')`). -/
def shearHomeo : ℝ × ℝ ≃ₜ ℝ × ℝ where
  toFun z := (z.1 + z.2, z.2)
  invFun z := (z.1 - z.2, z.2)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop


/-- The `τ'`-window at offset `x`:  `I ∩ (I − x) = [max(T−x, T), min(2T−x, 2T)]`
(§5.4: "= [T + x⁻, 2T − x⁺] for |x| < T", empty for `|x| > T`). -/
def Ix (T x : ℝ) : Set ℝ := Icc (max (T - x) T) (min (2 * T - x) (2 * T))








end Shear

/-! ## The inner `τ'`-integrals:  `∫_α^β cos(θt + c) dt`  (§5.4) -/

section CosIntegral


/-- Closed form of `J(θ,c;α,β) := ∫_α^β cos(θt + c) dt`:  `(β−α)cos c` if `θ = 0` (§5.4 "the first
inner integral is T−|x|"), else `[sin(θβ+c) − sin(θα+c)]/θ` (§5.4). -/
def Jker (θ c α β : ℝ) : ℝ :=
  if θ = 0 then (β - α) * Real.cos c else (Real.sin (θ * β + c) - Real.sin (θ * α + c)) / θ







variable {T : ℝ}


end CosIntegral

/-! ## Per-frequency-pair decomposition of `𝓜[cos(·y), cos(·y')]`  ([eq:MPP], §5.4) -/

section PairDecomp
variable {Φ : ℝ → ℝ} {T : ℝ}

/-- The "−" (difference-frequency) inner integral at offset x:  J(y−y', xy; I∩(I−x)). -/
def JmK (T y y' x : ℝ) : ℝ := Jker (y - y') (x * y) (max (T - x) T) (min (2 * T - x) (2 * T))
/-- The "+" (sum-frequency) inner integral at offset x:  J(y+y', xy; I∩(I−x)). -/
def JpK (T y y' x : ℝ) : ℝ := Jker (y + y') (x * y) (max (T - x) T) (min (2 * T - x) (2 * T))


/-- A⁻(y,y') := ∫_{[−T,T]} Φ(x)² J(y−y', xy) dx and A⁺(y,y') := ∫_{[−T,T]} Φ(x)² J(y+y', xy) dx:
the two halves of 𝓜[cos(·y),cos(·y')] ([eq:MPP]: first / second inner integral). -/
def Aminus (Φ : ℝ → ℝ) (T y y' : ℝ) : ℝ := ∫ x in Icc (-T) T, Φ x ^ 2 * JmK T y y' x
def Aplus (Φ : ℝ → ℝ) (T y y' : ℝ) : ℝ := ∫ x in Icc (-T) T, Φ x ^ 2 * JpK T y y' x



/-! ### The diagonal 𝒟 (§5.4) -/



/-! ### The sum-frequency terms 𝒪₂ (§5.4) -/


/-! ### The difference-frequency terms 𝒪₁, exact evaluation (§5.4) -/

/-- The four half-line trigonometric moments of Φ² (the paper's α_n^±, §5.4, split into
real and imaginary parts): C⁺(y) = ∫_0^T Φ²cos(xy), S⁺(y) = ∫_0^T Φ²sin(xy),
C⁻(y) = ∫_{−T}^0 Φ²cos(xy), S⁻(y) = ∫_{−T}^0 Φ²sin(xy). -/
def Cp (Φ : ℝ → ℝ) (T y : ℝ) : ℝ := ∫ x in (0:ℝ)..T, Φ x ^ 2 * Real.cos (x * y)
def Sp (Φ : ℝ → ℝ) (T y : ℝ) : ℝ := ∫ x in (0:ℝ)..T, Φ x ^ 2 * Real.sin (x * y)
def Cm (Φ : ℝ → ℝ) (T y : ℝ) : ℝ := ∫ x in (-T)..0, Φ x ^ 2 * Real.cos (x * y)
def Sm (Φ : ℝ → ℝ) (T y : ℝ) : ℝ := ∫ x in (-T)..0, Φ x ^ 2 * Real.sin (x * y)





end PairDecomp

/-! ## Applying H-MV on the prime-power frequencies  ([lem:MV], [eq:deltan]; §5.1, §5.4) -/

section MVapply
variable {C : ℝ}





end MVapply

end PrimeSide
end Zeta23


