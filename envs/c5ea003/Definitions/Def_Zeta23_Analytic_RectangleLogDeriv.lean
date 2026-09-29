-- Prove2me | Definitions.Def_Zeta23_Analytic_RectangleLogDeriv
-- name    : Zeta23_Analytic_RectangleLogDeriv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T19:59:28.420278+00:00
-- url     : https://prove2.me/theorems/ad582611-85f8-4a8a-8f7a-dc1a4c8c9ad1
-- title:
--   Rectangle residue calculus beyond one simple pole
-- statement:
--   This bundle sets up the module `Zeta23.Analytic.RectangleLogDeriv`, the project's residue calculus on rectangles beyond one simple pole; it contributes the namespace and import context (building on the `Rectangle` and `ResidueCalcOnRectangles` bundles) rather than new named definitions.
--
--   The theorems stated in this context are: `residueTheorem_finset` — if $f$ is holomorphic on a rectangle minus a finite set $S$ of interior points, with $f - A_p/(s - p)$ bounded near each $p \in S$, then the normalized rectangle contour integral equals $\sum_{p \in S} A_p$ (proved by induction on $S$: subtract one principal part, remove the singularity, recurse); and `rectangleIntegral'_mul_logDeriv`, the "argument principle with weight": for $f, g$ analytic near every point of the rectangle with $f \neq 0$ on the border,
--   $$\frac{1}{2\pi i}\oint g \cdot \frac{f'}{f} = \sum_{\rho \in Z} \mathrm{ord}_\rho(f)\, g(\rho),$$
--   where $Z$ is the finite zero set of $f$ in the rectangle. A meromorphic extension handles finitely many zeros *and* poles, intended for $f = $ `completedRiemannZeta` (simple poles at $0$ and $1$, residues $\mp 1$).
--
--   In the project this machinery drives the weighted contour integral $\oint H \cdot \Lambda'/\Lambda$ and the Riemann–von Mangoldt count $N(T_1,T_2) = \frac{1}{2\pi i}\oint \Lambda'/\Lambda$, feeding the zero-counting inputs (H-RvM) of Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Analytic/RectangleLogDeriv.lean

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Extra_Zeta23_Analytic_RectangleLogDeriv

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Residue calculus on rectangles beyond one simple pole.
Used for the weighted contour integral ∮ H·Λ'/Λ and for the Riemann–von Mangoldt count
N(T₁,T₂) = (1/2πi)∮ Λ'/Λ.

* `residueTheorem_finset`: f holomorphic on Rectangle z w minus a finite set S of interior points, with
  f − A p/(s − p) bounded near each p ∈ S  ⟹  RectangleIntegral' f z w = Σ_{p∈S} A p.
  (Induction on S: subtract one principal part, remove the singularity, recurse.)
* `rectangleIntegral'_mul_logDeriv` (the "argument principle with weight"): f, g analytic on a
  neighbourhood of each point of Rectangle z w, f ≠ 0 on the border, Z = the (finite) zero set of
  f in the rectangle  ⟹  RectangleIntegral' (g · f'/f) z w = Σ_{ρ∈Z} ord_ρ(f) · g(ρ).
* `finite_zeros_rectangle`, `rectangleIntegral'_mul_logDeriv'`: the zero set is finite; self-contained form.
-/

open Complex Set Topology Filter Asymptotics Real

noncomputable section

namespace Zeta23
namespace Analytic



/-! ## Meromorphic version: finitely many zeros AND poles inside the rectangle

Intended for f = completedRiemannZeta (simple poles at 0 and 1, residues ∓1):
(1/2πi) ∮ g·(f'/f) = Σ_{zeros ρ} ord_ρ(f)·g(ρ) − Σ_{poles p} m_p·g(p).
A pole of order m at p is witnessed elementarily by  (s − p)^m · f(s) → c ≠ 0  (s → p, s ≠ p),
which is the shape of Mathlib's `completedRiemannZeta_residue_one` (m = 1). -/





end Analytic
end Zeta23


