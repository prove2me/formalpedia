-- Prove2me | Definitions.Def_PNTA_ResidueRect
-- name    : PNTA_ResidueRect
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-12T05:41:25.593587+00:00
-- url     : https://prove2.me/theorems/33dc8c19-d6bd-41ca-aecd-bb9552770739
-- title:
--   Squares, functions with simple poles, and the residue at a point
-- statement:
--   Three small definitions used by the rectangle-contour residue calculus.
--
--   A **square** centred at $z$ with half-side $c$ is the axis-parallel rectangle
--   $$\mathrm{Square}(z, c) \;=\; \mathrm{Rectangle}(z - c - ci,\; z + c + ci),$$
--   i.e. the product of the real interval $[\,\mathrm{Re}\,z - c,\ \mathrm{Re}\,z + c\,]$ with the imaginary interval $[\,\mathrm{Im}\,z - c,\ \mathrm{Im}\,z + c\,]$.
--
--   A function $f$ **has simple poles on a set** $s$ when at every point $p \in s$ the function is meromorphic with a pole of order at most one — equivalently, the limit $\lim_{z \to p} (z - p) f(z)$ exists.
--
--   The **residue** of $f$ at $p$ is that limit,
--   $$\mathrm{res}_{p}(f) \;=\; \lim_{z \to p} (z - p)\, f(z),$$
--   which for a simple pole is the usual residue and which returns a junk value when no such limit exists.
--
--   These definitions give the vocabulary in which rectangle contour integrals are evaluated: the residue theorem on a rectangle states that the normalised boundary integral of a function with a single simple pole inside recovers the residue there.
--
--   **Formalization Note** The residue is defined as a limit rather than via a Laurent expansion, so it is total; the simple-pole hypothesis is what makes it agree with the classical notion.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Rectangle.lean#L39-L40 ; ResidueCalcOnRectangles.lean#L741-L761

/-
Extracted from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
commit f55e85551ac10e96d98262a354cfcaac2825f2da, Apache 2.0 license.
Wrapped in namespace PNTA for the Prove2Me platform.
-/

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Meromorphic.NormalForm

open Complex Set Topology
open scoped Interval
variable {z w : ℂ} {c : ℝ}

namespace PNTA

def Square (p : ℂ) (c : ℝ) : Set ℂ := Rectangle (-c - c * I + p) (c + c * I + p)

end PNTA


open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics
open scoped Interval
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

namespace PNTA

/-- Every pole of `f` in `s` is at most simple: the meromorphic order is `≥ -1` everywhere on `s`
(no poles of order `≤ -2`).

**Temporary scaffold.** The placeholder `residue` below (and Mathlib's current residue-theorem API)
is only correct for simple poles, so this hypothesis is added to Lemma 5.1 / Proposition 5.2 and
their sub-lemmas to make them provable with the present API. It holds in the intended applications
(e.g. `ζ'/ζ`, whose poles are all simple) and is to be removed once Mathlib gains general
higher-order residue support. -/
def HasSimplePolesOn (f : ℂ → ℂ) (s : Set ℂ) : Prop :=
  ∀ z ∈ s, (-1 : ℤ) ≤ meromorphicOrderAt f z

/-- **Placeholder definition — valid only for simple poles.** The residue of `f` at `z₀`, defined
as the simple-pole limit `lim_{z → z₀} (z - z₀) · f z` (matching the convention of
`Phi_circ.residue` / `Phi_star.residue`). At a point of analyticity this is `0` and at a simple
pole it is the usual residue, but at a higher-order or essential singularity the limit diverges
and this returns a junk value.

A general complex residue (and the residue theorem) is planned for Mathlib but not yet available,
so results stated in terms of this `residue` are likely **not provable in full generality** with
the current API. This is a deliberate stopgap, to be replaced with the robust notion once the
Mathlib residue-theorem API lands. -/
noncomputable def residue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  Filter.limUnder (nhdsWithin z₀ {z₀}ᶜ) (fun z ↦ (z - z₀) * f z)

end PNTA


