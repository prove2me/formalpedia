-- Prove2me | Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
-- name    : Zeta23_FromPNTPlus_ResidueCalcOnRectangles
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T19:58:14.126787+00:00
-- url     : https://prove2.me/theorems/fe5719ab-96b8-4989-9ccc-b7e429ace1c2
-- title:
--   Contour integrals over rectangles: $H$/$V$-integrals and `RectangleIntegral`
-- statement:
--   This bundle (ported from the PrimeNumberTheoremAnd project, file `ResidueCalcOnRectangles.lean`) defines the basic contour-integration vocabulary on rectangles in $\mathbb{C}$, for functions $f : \mathbb{C} \to E$ into a complex normed space.
--
--   **`HIntegral`** $f\,x_1\,x_2\,y := \int_{x_1}^{x_2} f(x + iy)\,dx$ (horizontal segment) and **`VIntegral`** $f\,x\,y_1\,y_2 := i\int_{y_1}^{y_2} f(x + iy)\,dy$ (vertical segment, with the orientation factor $i$). **`RectangleIntegral`** $f\,z\,w$ is the counterclockwise contour integral around the axis-parallel rectangle with corners $z, w$:
--   $$\oint = H(z.\mathrm{re}, w.\mathrm{re}, z.\mathrm{im}) - H(z.\mathrm{re}, w.\mathrm{re}, w.\mathrm{im}) + V(w.\mathrm{re}, z.\mathrm{im}, w.\mathrm{im}) - V(z.\mathrm{re}, z.\mathrm{im}, w.\mathrm{im}),$$
--   and **`RectangleIntegral'`** is the same divided by $2\pi i$. **`HolomorphicOn`** $f\,s$ abbreviates complex differentiability on the set $s$ (`DifferentiableOn ℂ f s`), and **`RectangleBorderIntegrable`** asserts interval-integrability of $f$ along all four sides.
--
--   The surrounding module proves the rectangle residue theorem for simple poles. In the project, this vocabulary is consumed by the `RectangleLogDeriv` development (finite-set residue theorem and the weighted argument principle $\frac{1}{2\pi i}\oint g\,f'/f = \sum_\rho \mathrm{ord}_\rho(f)g(\rho)$) and by the `ZetaBounds` port, i.e. the contour-integral computations behind the Riemann–von Mangoldt count.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/ResidueCalcOnRectangles.lean

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

/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes) and redirected intra-project
imports to Zeta23.FromPNTPlus.*.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    ∫ x in x₁..x₂, f (x + y * I)

noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    I • ∫ y in y₁..y₂, f (x + y * I)





/-- A `RectangleIntegral` of a function `f` is one over a rectangle
  determined by `z` and `w` in `ℂ`. -/
noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E :=
    HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im

/-- A `RectangleIntegral'` of a function `f` is one over a rectangle
  determined by `z` and `w` in `ℂ`, divided by `2 * π * I`. -/
noncomputable abbrev RectangleIntegral' (f : ℂ → E) (z w : ℂ) : E :=
    (1 / (2 * π * I)) • RectangleIntegral f z w

/- An UpperUIntegral is the integral of a function over a |\_| shape. -/

/- A LowerUIntegral is the integral of a function over a |-| shape. -/





/-- A function is `HolomorphicOn` a set if it is complex
  differentiable on that set. -/
abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop :=
    DifferentiableOn ℂ f s







def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im




































/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/








-- If two functions `f g : ℂ → ℂ` agree on a `codiscreteWithin R` full set, and `φ : ℝ → ℂ` is
-- an analytic non-constant path mapping `[a,b]` into `R`, then `∫ f(φ x) dx = ∫ g(φ x) dx`.
-- (a.e. agreement along the preimage suffices for interval integrals)

-- Under `HasSimplePolesOn f U`, every point with strictly negative meromorphic order has order
-- exactly -1: the simple-pole hypothesis gives `(-1 : ℤ) ≤ order`, negativity gives `order < 0`,
-- so the only integer fitting both is -1.

-- At a simple pole `p` of `f` inside `U`, the residue of the meromorphic normal form
-- `toMeromorphicNFOn f U` equals the residue of `f`. The two functions agree on a punctured
-- neighborhood of `p` (by definition of the normal form), so their `(z - p) * ·` limits coincide.

-- Non-constancy of horizontal paths `x ↦ x + h * I`.

-- Non-constancy of vertical paths `y ↦ r + y * I`.

-- Helper for horizontal integral congruence on codiscrete set

-- Helper for vertical integral congruence on codiscrete set

-- At the boundary, `f` and its normal-form representative differ only at a discrete set
-- of poles, so their boundary integrals coincide.





-- Since no poles lie on the boundary of the rectangle, the principal part is continuous
-- on the boundary and therefore integrable.



-- The integral of a sum of simple pole terms `c p / (s - p)` along the boundary of the rectangle
-- equals the sum of the coefficients `c p` for all points `p` in the interior.

-- Splits the integral of `fNF` into the integral of its holomorphic part and its principal part.


