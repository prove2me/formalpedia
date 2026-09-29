-- Prove2me | Definitions.Def_Geometry_AbstractAlgebra_FractalDimension
-- name    : Geometry_AbstractAlgebra_FractalDimension
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:33:36.221072+00:00
-- url     : https://prove2.me/theorems/a3dc7a8d-61bd-493b-993a-ef2da14f7e2a
-- title:
--   Aether Catalog definitions — Geometry_AbstractAlgebra_FractalDimension
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.AbstractAlgebra.FractalDimension`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/AbstractAlgebra/FractalDimension.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Set-Local Distortion of Hausdorff Dimension

This module develops the **set-local** theory of how the Hausdorff dimension of a
set is distorted under maps that are only assumed to be (anti)Lipschitz *on the set
itself*, rather than globally.

Mathlib already provides the global theory:
* `LipschitzOnWith.dimH_image_le` — Lipschitz-on-a-set maps do not increase dimension;
* `AntilipschitzWith.le_dimH_image` — *globally* antilipschitz maps do not decrease
  dimension.

What is missing is the genuinely set-local antilipschitz lower bound.  Mathlib has no
`AntilipschitzOnWith` predicate at all.  We introduce it and prove that a map which is
antilipschitz *only on `s`* still satisfies `dimH s ≤ dimH (f '' s)`.  Combined with the
Lipschitz-on upper bound this yields a clean set-local *bilipschitz invariance* of
Hausdorff dimension, and a set-local isometry invariance, neither of which follows from
the global Mathlib lemmas (which would require `f` to be antilipschitz on the *whole*
space).

Key results:
1. `AntilipschitzOnWith` — the set-local antilipschitz predicate.
2. `AntilipschitzOnWith.le_dimH_image` — the set-local dimension lower bound
   `dimH s ≤ dimH (f '' s)` (the headline theorem).
3. `dimH_image_eq_of_bilipschitzOn` — bilipschitz-on-a-set maps preserve dimension.
4. `dimH_image_eq_of_isometryOn` — isometry-on-a-set maps preserve dimension.
-/

open MeasureTheory Set

noncomputable section

variable {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]
variable {K K' : NNReal} {f : X → Y} {s t : Set X}

/-! ## The set-local antilipschitz predicate -/

-- !-- Lab Notebook -- !--
-- Hypothesis: The global `AntilipschitzWith.le_dimH_image` should have a set-local
--   analogue.  A map antilipschitz only on `s` cannot collapse `s`, so it must not
--   decrease the Hausdorff dimension of `s`.
-- Result: Confirmed.  The right vehicle is to restrict `f` to the subtype `s`, where
--   set-local antilipschitzness becomes *global* antilipschitzness, then transport via
--   the isometric inclusion `Subtype.val`.
-- Insight: `edist` on a subtype is *definitionally* the ambient `edist`, so the
--   restriction lemma is essentially free; all the work is bookkeeping of `'' univ`.
-- Failure analysis: A direct Hausdorff-measure argument (mirroring
--   `AntilipschitzWith.dimH_preimage_le`) is possible but would need a set-local
--   `hausdorffMeasure_preimage_le`, which Mathlib lacks; the subtype route avoids it.

/-- `AntilipschitzOnWith K f s` says that `f` is `K`-antilipschitz when restricted to the
set `s`: for all `x, y ∈ s`, `edist x y ≤ K * edist (f x) (f y)`.  This is the set-local
companion of `AntilipschitzWith`. -/
def AntilipschitzOnWith (K : NNReal) (f : X → Y) (s : Set X) : Prop :=
  ∀ ⦃x : X⦄, x ∈ s → ∀ ⦃y : X⦄, y ∈ s → edist x y ≤ K * edist (f x) (f y)

-- !-- A globally antilipschitz map is antilipschitz on every set (trivial specialisation). -- !--

-- !-- Restricting to a smaller set preserves the antilipschitz-on property. -- !--

-- !-- `edist (f x) (f y) = 0` forces `edist x y = 0`, hence `x = y` in an `EMetricSpace`. -- !--

/-! ## Reduction to a global antilipschitz map on the subtype -/

-- !-- The pulled-back map `x : s ↦ f x` is *globally* antilipschitz on the subtype `s`,
--     because subtype `edist` is definitionally the ambient `edist`. -- !--

/-! ## The headline theorem: set-local dimension lower bound -/

-- !-- Lab Notebook -- !--
-- Hypothesis: `AntilipschitzOnWith K f s → dimH s ≤ dimH (f '' s)`.
-- Result: Proved via the subtype reduction
--   `dimH s = dimH (univ : Set s) ≤ dimH ((f ∘ val) '' univ) = dimH (f '' s)`, using
--   `AntilipschitzWith.le_dimH_image`, `isometry_subtype_coe`, `Subtype.coe_image_univ`.
-- Insight: This is strictly stronger than the global Mathlib lemma — `f` may wildly
--   contract or even be non-injective *off* `s` and the bound still holds.

-- !-- Apply the subtype antilipschitz lemma + `AntilipschitzWith.le_dimH_image`, then
--     transport `dimH (univ : Set s) = dimH s` along the isometric inclusion. -- !--

/-! ## Bilipschitz and isometry invariance, set-locally -/

-- !-- Lab Notebook -- !--
-- Hypothesis: A map that is both Lipschitz-on and antilipschitz-on `s` preserves the
--   Hausdorff dimension of `s` exactly.
-- Result: Immediate from `LipschitzOnWith.dimH_image_le` (≤) and
--   `AntilipschitzOnWith.le_dimH_image` (≥) by antisymmetry.
-- Insight: Hausdorff dimension is a *bilipschitz-on invariant*, not merely a global
--   bilipschitz invariant.  This is the conceptual payload of the file.

-- !-- Antisymmetry of the Lipschitz-on upper bound and the antilipschitz-on lower bound. -- !--

-- !-- An isometry-on map satisfies both `LipschitzOnWith 1` and `AntilipschitzOnWith 1`. -- !--

-- !-- Combine `isometryOn_bilipschitz` with `dimH_image_eq_of_bilipschitzOn`. -- !--

end


