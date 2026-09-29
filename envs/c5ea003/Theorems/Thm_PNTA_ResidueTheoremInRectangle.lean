-- Prove2me | Theorems.Thm_PNTA_ResidueTheoremInRectangle
-- name    : PNTA.ResidueTheoremInRectangle
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T05:51:17.634579+00:00
-- url     : https://prove2.me/theorems/3c36f52e-c865-4d66-a275-2bcfc9a7c449
-- title:
--   Residue theorem on a rectangle: $\frac{1}{2\pi i}\oint \frac{c}{s-p}\,ds = c$
-- statement:
--   The residue theorem for a simple pole at an arbitrary interior point.
--
--   Let $z$ and $w$ be corners with $\mathrm{Re}\, z \le \mathrm{Re}\, w$ and $\mathrm{Im}\, z \le \mathrm{Im}\, w$, and let $p$ be a point in the interior of the rectangle with these opposite corners. Then for every constant $c \in \mathbb{C}$,
--   $$\frac{1}{2\pi i} \oint_{z}^{w} \frac{c}{s - p}\, ds \;=\; c .$$
--
--   The normalised contour integral of a simple pole recovers its residue exactly. This is the form in which the residue theorem enters Perron-formula arguments: after a contour is pulled across a pole of $\zeta'/\zeta$ or of a Mellin transform, this identity converts the crossing into the residue's contribution to the main term.
--
--   **Formalization Note** The hypothesis that $p$ lies in the interior is stated as the rectangle being a neighbourhood of $p$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L583-L594

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
import Definitions.Def_ResidueCalcOnRectangles_defs

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics
open scoped Interval
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

theorem PNTA.ResidueTheoremInRectangle
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s => c / (s - p)) z w = c := by sorry
