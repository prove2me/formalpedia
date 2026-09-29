-- Prove2me | Theorems.Thm_verticalIntegral_split_three
-- name    : verticalIntegral_split_three
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:06:08.253364+00:00
-- url     : https://prove2.me/theorems/3eec380a-60db-4596-9395-2f1f24c91d2f
-- title:
--   Splitting a vertical line integral into lower tail, middle segment, and upper tail
-- statement:
--   Let $f : \mathbb{C} \to \mathbb{C}$, let $\sigma \in \mathbb{R}$ be the abscissa of a vertical line, and let $a, b \in \mathbb{R}$. Assume the function $t \mapsto f(\sigma + ti)$ is integrable on $\mathbb{R}$. Write $\int_{(\sigma)} f$ for the vertical integral $i \int_{-\infty}^{\infty} f(\sigma + ti)\,dt$ and $\mathrm{VIntegral}(f, \sigma, a, b) = i\int_a^b f(\sigma+ti)\,dt$ for its finite middle piece. Then the full vertical integral decomposes as
--
--   $$\int_{(\sigma)} f \;=\; i \int_{-\infty}^{a} f(\sigma + ti)\,dt \;+\; i \int_{a}^{b} f(\sigma + ti)\,dt \;+\; i \int_{b}^{\infty} f(\sigma + ti)\,dt,$$
--
--   with the tails taken over $(-\infty, a]$ and $[b, \infty)$ respectively.
--
--   This three-way splitting is the standard first step in estimating Perron/Mellin-type integrals in the proof of the Prime Number Theorem: the finite middle segment $[a, b]$ (typically $|t| \le T$) is treated by contour shifting and zero-free-region bounds, while the two infinite tails are bounded using the decay of the Mellin transform of the smoothing kernel. The lemma packages the required integrability bookkeeping so downstream estimates can address the three pieces independently.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L65-L73

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

theorem verticalIntegral_split_three (a b : ℝ)
    (hf : Integrable (fun t : ℝ ↦ f (σ + t * I))) :
    VerticalIntegral f σ =
      I • (∫ t in Iic a, f (σ + t * I)) + VIntegral f σ a b +
      I • ∫ t in Ici b, f (σ + t * I) := by sorry
