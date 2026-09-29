-- Prove2me | Theorems.Thm_existsDifferentiableOn_of_bddAbove
-- name    : existsDifferentiableOn_of_bddAbove
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:43:35.071306+00:00
-- url     : https://prove2.me/theorems/055a83c6-117a-43bc-9628-464349ac924e
-- title:
--   Riemann's removable singularity theorem: a bounded holomorphic function extends across an isolated puncture
-- statement:
--   Let $E$ be a complete normed complex vector space, let $S \subseteq \mathbb{C}$ be a neighborhood of a point $c$, and let $f : \mathbb{C} \to E$ be holomorphic on the punctured set $S \setminus \{c\}$. Assume that $f$ is bounded there, i.e. the set $\{\, \|f(z)\| : z \in S \setminus \{c\} \,\}$ is bounded above. Then the singularity at $c$ is removable:
--
--   $$\exists\, g : \mathbb{C} \to E \text{ holomorphic on } S \ \text{ with } \ g = f \text{ on } S \setminus \{c\}.$$
--
--   This is the classical Riemann removable singularity theorem, packaged for a set $S$ that is merely a neighborhood of $c$ (not necessarily open everywhere), and for vector-valued holomorphic functions.
--
--   In the rectangle-contour residue calculus of the project, this lemma is the basic tool for trading a function with an isolated (but harmless) singularity for a genuinely holomorphic one, so that Cauchy-type integral theorems over rectangles can be applied without special-casing the puncture.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L92-L101

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

theorem existsDifferentiableOn_of_bddAbove [CompleteSpace E]
    {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c}))
    (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E),
      HolomorphicOn g s ∧ Set.EqOn f g (s \ {c}) := by sorry
