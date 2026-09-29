-- Prove2me | Theorems.Thm_Zeta23_IsBigO_to_BddAbove
-- name    : Zeta23_IsBigO_to_BddAbove
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:37:51.695086+00:00
-- url     : https://prove2.me/theorems/6a71d8d2-a526-4869-9f4b-0cd93890e27e
-- title:
--   A function that is $O(1)$ near a point is bounded on a punctured neighbourhood
-- statement:
--   Let $f : \mathbb{C} \to \mathbb{C}$ and $p \in \mathbb{C}$, and suppose $f = O(1)$ along the punctured neighbourhood filter $\mathcal{N}_{\ne}(p)$ (Lean: `f =O[𝓝[≠] p] 1`).
--
--   Then there exists a neighbourhood $U$ of $p$ such that the set of values $\{\|f(z)\| : z \in U \setminus \{p\}\}$ is bounded above:
--   $$\exists\, U \in \mathcal{N}(p),\quad \operatorname{BddAbove}\bigl(\|f\|\,(U \setminus \{p\})\bigr).$$
--
--   This is a filter-language bookkeeping lemma converting an asymptotic big-O statement into a concrete bound on a punctured neighbourhood. In the module `Zeta23.FromPNTPlus.ResidueCalcOnRectangles` it feeds the rectangle residue theorem `Zeta23.Analytic.residueTheorem_finset`, where the hypothesis that $f(s) - A_p/(s - p)$ is $O(1)$ near each pole $p$ must be turned into boundedness in order to invoke removable-singularity arguments.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/ResidueCalcOnRectangles.lean#L556-L573

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

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics
open scoped Interval
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

theorem Zeta23_IsBigO_to_BddAbove {f : ℂ → ℂ} {p : ℂ}
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by sorry
