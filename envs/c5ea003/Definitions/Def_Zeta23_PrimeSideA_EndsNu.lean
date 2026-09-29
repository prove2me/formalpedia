-- Prove2me | Definitions.Def_Zeta23_PrimeSideA_EndsNu
-- name    : Zeta23_PrimeSideA_EndsNu
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:17:33.019833+00:00
-- url     : https://prove2.me/theorems/9b18e563-eebb-446f-8f91-6e58ead1eb90
-- title:
--   Grid sum $S(\Delta)$ and half-line majorants for the $\nu$-weighted estimate N2
-- statement:
--   This bundle provides the majorant machinery for N2 (`nu_grid_bound`), the second of the two one-dimensional $\nu$-weighted $\psi$ estimates of §5.3 feeding the $\mathcal{E}_2$ bound of [lem:ends]: $\int_{\mathbb{R} \setminus I} |\nu_X(\tau)|\, \sigma(\tau)\, d\tau \le C_{N2}(c_\varrho)\, B\, L\, l$, where $\sigma(\tau) := \sum_{k<d} \psi(\tau - \tau_k)$ and $B = l + 4\sqrt{X}$.
--
--   The members: `CN2` is the explicit N2 constant $100(1 + |\log c_\varrho| + |c_\varrho|)$ (depending on $c_\varrho$ only; its value is immaterial). `Sgrid` is $\sigma$ reduced to the half-line: $S(\Delta) := \sum_{j < d} \psi(\Delta + jh)$, where $\Delta$ is the distance to the window and $h$ the grid spacing. `Mnear` and `Mfar` are the half-line majorants: in the near range ($\Delta \le 2T$, where $|\nu| \le B$),
--   $$M_{\mathrm{near}}(\Delta) := B \Bigl( \psi(\Delta) + \frac{L}{2\pi} \min\Bigl( \int_0^\infty \psi,\ \frac{c_\varrho}{w \Delta} \Bigr) \Bigr),$$
--   and in the far range ($\Delta > 2T$, where $|\nu| \le B + 2\sqrt{\Delta/T}$),
--   $$M_{\mathrm{far}}(\Delta) := d\, \frac{c_\varrho}{w \Delta^2}\, \Bigl( B + 2\sqrt{\Delta/T} \Bigr);$$
--   `Mtot` glues them by indicator functions on $(0, 2T]$ and $(2T, \infty)$.
--
--   Role: the pointwise bounds $S(\Delta) \le \psi(\Delta) + (L/2\pi)\min(\Psi', c/(w\Delta))$ (near) and $S(\Delta) \le d\,c/(w\Delta^2)$ (far), combined with the $\nu_X$ bound of [eq:Bdef], dominate the N2 integrand by `Mtot`; integrating `Mtot` gives the $\ll B L l$ bound consumed by `Zeta23/PrimeSideA/EndsE2.lean`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsNu.lean

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideA_EndsCore

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — [lem:ends], the two one-dimensional ν-weighted ψ estimates feeding the 𝓔₂ bound
(§5.3 of the paper).  Consumed by Zeta23/PrimeSideA/EndsE2.lean.

* N1 `nu_weight_bound` (§5.3: "In the second factor, the range |τ'−τ_k| ≤ 2T has |τ'| ≤ 4T and
  contributes at most 2Ψ₀B; on |τ'−τ_k| =: r > 2T we have |τ'| ≤ 2r, |ν_X(τ')| ≤ B + log(r/T) and
  ψ(r) ≤ c_ϱ r⁻², contributing ≪ B/T. So the second factor is ≤ 3Ψ₀B uniformly in k."):
      ∫_ℝ ψ(τ−a) |ν_X(τ)| dτ ≤ (2Ψ + 5c_ϱ)·B   for a ∈ I = [T,2T],  Ψ := 4 + 2 log(c_ϱL/4w) ≥ Ψ₀.
  Route (constants only differ): |ν_X(τ)| ≤ B + log⁺(|τ|/4T) ≤ B + 2√(|τ|/4T) ≤ B + 2 + 2√(|τ−a|/4T)
  for |a| ≤ 2T, so the integral is ≤ (B+2)∫ψ + T^{-1/2}∫ψ(r)√|r| dr ≤ (B+2)·2Ψ + 2L + 4c_ϱ/w.
* N2 `nu_grid_bound` (§5.3: "The sum over k of the first factor equals ∫_{τ∉I}|ν_X(τ)|σ(τ)dτ with
  σ(τ) := Σ_{k<d} ψ(τ−τ_k) … Hence ∫_{τ∉I}|ν_X|σ ≪ BLl"):
      ∫_{ℝ∖I} |ν_X(τ)| σ(τ) dτ ≤ CN2(c_ϱ)·B·L·l.
Here ψ = `psiA cϱ p` [eq:psidef], B = `B` = l + 4√X and `NuBound p` = [eq:Bdef]
(discharged by nuX_abs_le), all from Zeta23/PrimeSideA/EndsCore.lean.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Real Set

namespace Zeta23
namespace PrimeSide

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

/-- The constant of N2 (depends on c_ϱ only; explicit, value immaterial). -/
def CN2 (cϱ : ℝ) : ℝ := 100 * (1 + |Real.log cϱ| + |cϱ|)








/-! ### N2: reduction to the half-line and the majorant -/



/-- σ reduced to the half-line: S(Δ) := Σ_{j<d} ψ(Δ + jh)  (§5.3). -/
def Sgrid (cϱ : ℝ) (p : Setting) (Δ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range p.d, psiA cϱ p (Δ + j * p.h)








/-- The half-line majorants (§5.3).  Near: Δ ≤ 2T, |ν| ≤ B and
S(Δ) ≤ ψ(Δ) + (L/2π)min(Ψ', c/(wΔ));  far: Δ > 2T, |ν| ≤ B + 2√(Δ/T) and S(Δ) ≤ d c/(wΔ²). -/
def Mnear (cϱ : ℝ) (p : Setting) (B : ℝ) (Δ : ℝ) : ℝ :=
  B * (psiA cϱ p Δ + p.L / (2 * π) * min (∫ r in Ioi 0, psiA cϱ p r) (cϱ / (p.w * Δ)))

def Mfar (cϱ : ℝ) (p : Setting) (B : ℝ) (Δ : ℝ) : ℝ :=
  p.d * (cϱ / (p.w * Δ ^ 2)) * (B + 2 * Real.sqrt (Δ / p.T))

def Mtot (cϱ : ℝ) (p : Setting) (B : ℝ) (Δ : ℝ) : ℝ :=
  (Ioc 0 (2 * p.T)).indicator (Mnear cϱ p B) Δ + (Ioi (2 * p.T)).indicator (Mfar cϱ p B) Δ








/-! ### N2: integrating the majorant -/













end PrimeSide
end Zeta23


