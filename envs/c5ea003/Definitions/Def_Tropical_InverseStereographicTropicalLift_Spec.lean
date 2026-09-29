-- Prove2me | Definitions.Def_Tropical_InverseStereographicTropicalLift_Spec
-- name    : Tropical_InverseStereographicTropicalLift_Spec
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:30:17.630649+00:00
-- url     : https://prove2.me/theorems/ca88942f-688a-41ea-b9e2-c744ef567a13
-- title:
--   Aether Catalog definitions — Tropical_InverseStereographicTropicalLift_Spec
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.InverseStereographicTropicalLift.Spec`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/InverseStereographicTropicalLift/Spec.lean by skeleton subtraction
import Mathlib

/-!
# Inverse Stereographic Tropical Lift

This file separates two standard conventions for the tropical projective line.
The **finite** line uses only finite tropical coordinates.  After quotienting
`(x₀,x₁)` by simultaneous translation, its canonical coordinate is `x₁-x₀`,
so it is represented here by `ℝ`.  The **compactified** line permits an infinite
endpoint and is represented by `EReal`.

For the finite line, the pole-inspired max-plus rational expression

`max (2x) x - max x 0`

looks quadratic but simplifies globally to `x`.  It is consequently a
homeomorphism.  This also disproves the stronger claim that its *minimal*
tropical rational degree is exactly two: it already has a linear presentation.
For the compactified convention, no homeomorphism to `ℝ` can exist, by
compactness.
-/

namespace InverseStereographicTropicalLift

/-- The finite tropical projective line in its canonical normalized coordinate
`x₁ - x₀`. -/
abbrev FiniteTP1 := ℝ

/-- The compactified tropical projective line, obtained by allowing infinite
coordinates before projectivization. -/
abbrev CompactifiedTP1 := EReal

/-- The quadratic-over-linear max-plus expression proposed as the tropical
stereographic pole construction. -/
def tropicalStereo (x : FiniteTP1) : ℝ :=
  max (2 * x) x - max x 0

/-- A function has the particular quadratic tropical rational shape relevant
for the pole construction.  Coefficients are finite and the displayed leading
quadratic term is present. -/
def HasQuadraticTropicalPresentation (f : ℝ → ℝ) : Prop :=
  ∃ a b c d : ℝ, ∀ x, f x = max (2 * x + a) (x + b) - max (x + c) d

/-- A function has a degree-at-most-one tropical presentation if it is an
ordinary translation in the normalized tropical coordinate. -/
def HasLinearTropicalPresentation (f : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ x, f x = x + c


/-- Moving the tropical pole to `p` gives the corresponding family of
quadratic-over-linear expressions. -/
def tropicalStereoAt (p x : ℝ) : ℝ :=
  max (2 * x) (x + p) - max x p









end InverseStereographicTropicalLift


