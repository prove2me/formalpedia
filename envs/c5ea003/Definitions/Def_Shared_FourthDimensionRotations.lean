-- Prove2me | Definitions.Def_Shared_FourthDimensionRotations
-- name    : Shared_FourthDimensionRotations
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:35:56.314452+00:00
-- url     : https://prove2.me/theorems/679d667c-bee1-4595-8020-e9c464f1cd3c
-- title:
--   Aether Catalog definitions — Shared_FourthDimensionRotations
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.FourthDimensionRotations`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/FourthDimensionRotations.lean by skeleton subtraction
import Mathlib

/-!
# Smooth phase rotations in four dimensions

This file deepens `FourthDimensionPlayground` by replacing its single quarter-turn
with the full circle action on `ℂ²`.  Unit complex phases act by smooth linear
rotations, preserve every centered three-sphere and every Hopf fibre, compose as
the circle group does, and every nonidentity phase is fixed-point-free away from
the origin.
-/

open ComplexConjugate

namespace FourthDimensionPlayground

/-- Simultaneous multiplication by a complex phase on the `ℂ²` model of `ℝ⁴`. -/
def phaseRotation (u : ℂ) (p : ℂ × ℂ) : ℂ × ℂ := (u * p.1, u * p.2)









end FourthDimensionPlayground


