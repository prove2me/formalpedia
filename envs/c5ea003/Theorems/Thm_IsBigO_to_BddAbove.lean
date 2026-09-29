-- Prove2me | Theorems.Thm_IsBigO_to_BddAbove
-- name    : IsBigO_to_BddAbove
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:40:27.971148+00:00
-- url     : https://prove2.me/theorems/9679d93e-eb72-4a91-9e81-ff4618976134
-- title:
--   A function that is $O(1)$ at a punctured point is bounded on a punctured neighborhood
-- statement:
--   Let $f\colon\mathbb{C}\to\mathbb{C}$ and let $p\in\mathbb{C}$. Suppose $f$ is big-O of the constant function $1$ along the punctured neighborhood filter at $p$, i.e. $f=O(1)$ as $s\to p$, $s\ne p$. Then boundedness holds on an actual set: there exists a neighborhood $U$ of $p$ such that
--
--   $$\{\,\|f(s)\| : s\in U\setminus\{p\}\,\}\ \text{is bounded above.}$$
--
--   This is a routine but frequently needed unfolding of the filter-language statement $f=O_{\,s\to p,\ s\neq p}(1)$ into the set-language statement that $\|f\|$ admits an upper bound on some punctured neighborhood $U\setminus\{p\}$.
--
--   In the residue-calculus toolkit of this development it serves as the bridge between the asymptotic characterization of a removable-singularity-plus-simple-pole expansion (stated as a big-O condition) and the explicit bounded-difference form consumed by the rectangle residue theorem. It is completely general and reusable wherever a `IsBigO` hypothesis at a punctured point must be converted to a `BddAbove` statement.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L542-L559

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

theorem IsBigO_to_BddAbove {f : ℂ → ℂ} {p : ℂ}
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by sorry
