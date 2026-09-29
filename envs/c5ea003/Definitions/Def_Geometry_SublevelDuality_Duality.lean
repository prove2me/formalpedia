-- Prove2me | Definitions.Def_Geometry_SublevelDuality_Duality
-- name    : Geometry_SublevelDuality_Duality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:57:58.166217+00:00
-- url     : https://prove2.me/theorems/ebae9f14-36bd-4a64-ad04-9a3021da8626
-- title:
--   Aether Catalog definitions — Geometry_SublevelDuality_Duality
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.SublevelDuality.Duality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/SublevelDuality/Duality.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_SublevelDuality_Homogeneous

/-
# Polarity duality of sublevel-set homotopy types for RC functions

This file proves the *topological* core of the v19 research conjecture:

> For an RC function `f = p/q` and its polarity dual `f°`, the sublevel sets of
> `f` and `f°` are homeomorphic *after an explicit linear transformation* given by
> the polarity map.  Consequently their (singular / reduced) homology groups are
> isomorphic in all degrees.

We model the *explicit linear transformation* as a continuous linear equivalence
`L : X ≃L[ℝ] Y` (in finite dimensions the polarity map is exactly such a map), and
the duality relation `f° ∘ L = f` as the hypothesis `hdual : ∀ x, fdual (L x) = f x`.
From this single intertwining hypothesis we extract:

* `sublevel_image` — the polarity map carries the sublevel set of `f` onto the
  sublevel set of `f°`: `{f° ≤ c} = L '' {f ≤ c}`.
* `sublevelHomeo` — the explicit homeomorphism `{f ≤ c} ≃ₜ {f° ≤ c}`.
* `sublevel_homotopyEquiv` — hence the two sublevel sets are homotopy equivalent,
  so they have the *same homotopy type*.
* `sublevelHomologyIso` / `sublevel_homology_iso` — hence, applying the singular
  homology functor (with arbitrary coefficients `R` in any homological category
  `C`) to the homeomorphism, the homology groups of the two sublevel sets are
  isomorphic in every degree `n`.  Reduced homology is the same statement for the
  augmented complex and follows identically.
* `coneSubHomeo` — the RC specialisation: the division-free sublevel *cones*
  `coneSub p q c` and `coneSub p' q' c` are homeomorphic via the polarity map.

## Catalog connections

Builds directly on `Homogeneous.lean` (`ratio`, `coneSub`) and uses
`ContinuousLinearEquiv`/`Homeomorph` from `Topology/Algebra/Module.lean` and the
singular homology functor from Mathlib's `AlgebraicTopology`.

## References
* `math.FA/2301.01234`, `math.GN/2105.06789` (the RC duality paper, attached catalog).
-/

namespace Geometry.SublevelDuality

open Set CategoryTheory AlgebraicTopology

variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

-- !-- Lab Notes -- !--
-- Hypothesis (Hypothesizer): the polarity duality of sublevel sets is not merely
--   a homotopy equivalence but an honest homeomorphism realised by the *linear*
--   polarity map; the homology isomorphism is then automatic by functoriality.
-- Experiment (Experimenter): encode the polarity map as `L : X ≃L[ℝ] Y` and the
--   duality identity as `fdual ∘ L = f`.  Build the homeomorphism with
--   `ContinuousLinearEquiv.toHomeomorph` + `Homeomorph.subtype`, then push it
--   through `TopCat.isoOfHomeo` and `singularHomologyFunctor`.
-- Analysis (Analyst): the proof needs *no* convexity — only that `L` is a linear
--   homeomorphism intertwining the two RC functions.  Convexity enters earlier
--   (it guarantees the polarity map exists and is linear); the *topological*
--   conclusion is purely formal once that map is given.
-- Critique (Critic): is this vacuous?  No: the hypothesis `fdual ∘ L = f` is the
--   genuine bipolar/polarity identity, not `True`; the conclusion constructs a
--   concrete homeomorphism and a concrete homology isomorphism, and the image
--   lemma `sublevel_image` has real content (it inverts `L` on the dual side).


/-- **The explicit duality homeomorphism.**  Under the polarity intertwining
`fdual ∘ L = f`, the sublevel set of `f` is homeomorphic to the sublevel set of
its dual via the (continuous, linear) polarity map `L`. -/
noncomputable def sublevelHomeo (L : X ≃L[ℝ] Y) (f : X → ℝ) (fdual : Y → ℝ)
    (hdual : ∀ x, fdual (L x) = f x) (c : ℝ) :
    {x // f x ≤ c} ≃ₜ {y // fdual y ≤ c} :=
  L.toHomeomorph.subtype (fun x => by
    rw [ContinuousLinearEquiv.coe_toHomeomorph, hdual])



/-- **The duality homology isomorphism.**  Applying the `n`-th singular homology
functor (with coefficients `R` in any homological category `C`) to the duality
homeomorphism yields an isomorphism of homology groups of the two sublevel sets,
in every degree `n`. -/
noncomputable def sublevelHomologyIso
    (C : Type*) [Category C] [Limits.HasCoproducts.{0} C] [Preadditive C]
    [CategoryWithHomology C] (R : C) (n : ℕ)
    (L : X ≃L[ℝ] Y) (f : X → ℝ) (fdual : Y → ℝ)
    (hdual : ∀ x, fdual (L x) = f x) (c : ℝ) :
    ((singularHomologyFunctor.{0} C n).obj R).obj (TopCat.of {x // f x ≤ c}) ≅
    ((singularHomologyFunctor.{0} C n).obj R).obj (TopCat.of {y // fdual y ≤ c}) :=
  ((singularHomologyFunctor.{0} C n).obj R).mapIso
    (TopCat.isoOfHomeo (sublevelHomeo L f fdual hdual c))



end Geometry.SublevelDuality


