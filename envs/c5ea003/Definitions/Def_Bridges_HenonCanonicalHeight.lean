-- Prove2me | Definitions.Def_Bridges_HenonCanonicalHeight
-- name    : Bridges_HenonCanonicalHeight
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:23:50.351597+00:00
-- url     : https://prove2.me/theorems/886e0a90-45d0-4a6f-bddf-d441f09269f3
-- title:
--   Aether Catalog definitions — Bridges_HenonCanonicalHeight
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.HenonCanonicalHeight`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/HenonCanonicalHeight.lean by skeleton subtraction
import Mathlib

/-!
# Escape regions and normalized heights for a Hénon map

This file formalizes algebraic and analytic ingredients used in the study of the map
`φ(x,y) = (y, x + y^D + b)`.  The escape region below is a slightly strengthened,
robust version of the usual archimedean escape region: the additional condition
`3 |y| < |y|^D` makes forward invariance transparent even in the presence of
cancellation.  No global arithmetic-height machinery is assumed.
-/

namespace HenonCanonicalHeight

/-- The normalized Hénon map `φ(x,y) = (y, x + y^D + b)`. -/
def henon (D : ℕ) (b : ℝ) (P : ℝ × ℝ) : ℝ × ℝ :=
  (P.2, P.1 + P.2 ^ D + b)

/-- The polynomial inverse of `henon`. -/
def henonInv (D : ℕ) (b : ℝ) (P : ℝ × ℝ) : ℝ × ℝ :=
  (P.2 - P.1 ^ D - b, P.1)



/-- A robust archimedean forward escape region.  Its first inequality says the
new nonlinear term dominates both possible error terms and `1`; its second says
that one third of the nonlinear term is already larger than the old coordinate. -/
def InForwardRegion (D : ℕ) (b : ℝ) (P : ℝ × ℝ) : Prop :=
  3 * max (max |P.1| |b|) 1 < |P.2| ^ D ∧
  3 * |P.2| < |P.2| ^ D



/-- A robust backward escape region, obtained by exchanging the coordinates. -/
def InBackwardRegion (D : ℕ) (b : ℝ) (P : ℝ × ℝ) : Prop :=
  3 * max (max |P.2| |b|) 1 < |P.1| ^ D ∧
  3 * |P.1| < |P.1| ^ D




end HenonCanonicalHeight


