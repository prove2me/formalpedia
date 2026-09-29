-- Prove2me | Definitions.Def_Extra_Zeta23_Analytic_RectangleLogDeriv
-- name    : Extra_Zeta23_Analytic_RectangleLogDeriv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T19:58:38.806341+00:00
-- url     : https://prove2.me/theorems/65c395c1-d94c-4905-a5e8-6e65e42d5cf8
-- title:
--   Context for rectangle residue calculus with weights
-- statement:
--   This bundle is a context/scaffolding file: it introduces no new definitions of its own. It opens the namespace `Zeta23.Analytic` and assembles the import context (the `Rectangle` and `ResidueCalcOnRectangles` definition bundles from the PNT+ port, together with the relevant Mathlib analysis libraries) in which the project's rectangle residue calculus beyond one simple pole is developed.
--
--   The development it supports proves, on a rectangle with corners $z, w \in \mathbb{C}$: a finite-set residue theorem ($f$ holomorphic off a finite interior set $S$, with $f - A_p/(s-p)$ bounded near each $p \in S$, gives $\frac{1}{2\pi i}\oint f = \sum_{p \in S} A_p$), and the *weighted argument principle* $\frac{1}{2\pi i}\oint g\,\frac{f'}{f} = \sum_{\rho} \mathrm{ord}_\rho(f)\, g(\rho)$ over the (finite) zero set of $f$ in the rectangle, including a meromorphic version tracking finitely many poles (intended for the completed zeta function $\Lambda$, with simple poles at $0$ and $1$).
--
--   In the project this layer underlies the weighted contour integral $\oint H \cdot \Lambda'/\Lambda$ and the Riemann–von Mangoldt count $N(T_1,T_2) = \frac{1}{2\pi i}\oint \Lambda'/\Lambda$ used in the zero-counting side of Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260

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


