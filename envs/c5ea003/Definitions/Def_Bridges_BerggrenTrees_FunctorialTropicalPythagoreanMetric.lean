-- Prove2me | Definitions.Def_Bridges_BerggrenTrees_FunctorialTropicalPythagoreanMetric
-- name    : Bridges_BerggrenTrees_FunctorialTropicalPythagoreanMetric
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:24:57.439447+00:00
-- url     : https://prove2.me/theorems/16773c10-89d4-4ba3-82e8-84bf740033f7
-- title:
--   Aether Catalog definitions — Bridges_BerggrenTrees_FunctorialTropicalPythagoreanMetric
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.BerggrenTrees.FunctorialTropicalPythagoreanMetric`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/BerggrenTrees/FunctorialTropicalPythagoreanMetric.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_BerggrenTrees_BerggrenBoundaryUltrametric
/-
  # Metric-Space Packaging of the Berggren Boundary Ultrametric (Conjecture C1)

  Bridge: connects the bespoke tree ultrametric `d` of
  `Bridges.FunctorialTropicalPythagorean` to Mathlib's first-class metric infrastructure.

  This file discharges the *metric-space packaging* half of conjecture **C1**: the boundary
  `Addr = ℕ → Fin 3` of the ternary Berggren tree, equipped with `d`, underlies a genuine
  Mathlib `MetricSpace`, and `d` is registered as an `IsUltrametricDist`. This unlocks the
  entire Mathlib metric API (balls, continuity, the ultrametric ball lemmas) for the
  Pythagorean-Berggren boundary.

  -- !-- Lab Notes -- !--
  HYPOTHESIS (Hypothesizer): the six ultrametric axioms already proven (`d_self`, `d_comm`,
  `d_eq_zero_iff`, `d_triangle`, `d_ultra`, `d_le_one`) are *exactly* the data Mathlib needs
  for a `MetricSpace` plus `IsUltrametricDist`; nothing else is required for packaging.
  EXPERIMENT (Experimenter): assemble `MetricSpace Addr` from `d_self`/`d_comm`/`d_triangle`/
  `d_eq_zero_iff`, then `IsUltrametricDist Addr` from `d_ultra`, then re-derive the half-scale
  similarity and the bounded-diameter facts through the Mathlib `dist`.
  ANALYSIS (Analyst): the packaging is purely structural — the only subtlety is that the
  `IsUltrametricDist` field uses the `max (dist x y) (dist y z)` ordering, which is precisely
  `d_ultra`. The instance is `noncomputable` because `d` is.
  CRITIQUE (Critic): completeness/compactness (the Cantor-space half of C1) is *not* claimed
  here; only the metric/ultrametric packaging is. We flag this explicitly so the result is
  not over-stated. `dist_cons_same` is genuine content (the contraction factor through the
  Mathlib `dist`), not a restatement of an instance field.
  SYNTHESIS (PI): with `Addr` now a bona fide ultrametric space, the remaining C1 work
  (totally bounded + complete ⇒ compact) is a clean follow-up recorded in FUTURE_DIRECTIONS.
-/


namespace FunctorialTropicalPythagorean

open CategoricalTropicalUltrametric
open Classical

/-- The Berggren boundary `Addr` is a Mathlib `MetricSpace` with distance `d`. -/
noncomputable instance instMetricSpaceAddr : MetricSpace Addr where
  dist := d
  dist_self := d_self
  dist_comm := d_comm
  dist_triangle := d_triangle
  eq_of_dist_eq_zero := fun {x y} h => (d_eq_zero_iff x y).mp h


/-- The Berggren boundary is an ultrametric space (strong triangle inequality). -/
instance instIsUltrametricDistAddr : IsUltrametricDist Addr :=
  ⟨fun x y z => d_ultra x y z⟩





end FunctorialTropicalPythagorean


