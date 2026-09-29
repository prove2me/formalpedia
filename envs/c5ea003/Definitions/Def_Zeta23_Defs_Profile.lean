-- Prove2me | Definitions.Def_Zeta23_Defs_Profile
-- name    : Zeta23_Defs_Profile
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:03:04.423652+00:00
-- url     : https://prove2.me/theorems/65075878-5c70-4e5c-9b5e-e92babba5fb2
-- title:
--   The standard taper profile via `Real.smoothTransition`
-- statement:
--   This bundle defines **`stdProfile`**, the canonical taper profile used by the headline theorems: it is Mathlib's `Real.smoothTransition`, a $C^\infty$ nondecreasing function $\varrho : \mathbb{R} \to \mathbb{R}$ with $\varrho = 0$ on $(-\infty, 0]$ and $\varrho = 1$ on $[1, \infty)$.
--
--   The paper fixes "once and for all a nondecreasing function $\varrho \in C^3(\mathbb{R})$ with $\varrho = 0$ on $(-\infty,0]$ and $\varrho = 1$ on $[1,\infty)$" [subsec:family]; since `Real.smoothTransition` is such a function (indeed smooth, hence $C^3$), the headline theorems can use this concrete choice and need not quantify over $\varrho$. The taper $\varphi(u) = \varrho((L/2 - |u|)/w)$ of `Defs.lean` is built from it, so this definition anchors the concrete statements of Theorems A, B, C.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Defs/Profile.lean, docstring tag [subsec:family]

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
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
Zeta23/Defs/Profile.lean — a concrete taper profile.
The paper: "Fix once and for all a nondecreasing function ϱ ∈ C³(ℝ) with ϱ = 0 on (−∞,0] and ϱ = 1 on
[1,∞)" [subsec:family]. Mathlib's Real.smoothTransition is such a function (even C^∞), so the
headline theorems need not quantify over ϱ.
-/

noncomputable section

namespace Zeta23


/-- The canonical profile used for the headline theorems. -/
def stdProfile : ℝ → ℝ := Real.smoothTransition



end Zeta23


