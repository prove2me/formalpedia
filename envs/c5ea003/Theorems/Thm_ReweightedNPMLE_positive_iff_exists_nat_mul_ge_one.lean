-- Prove2me | Theorems.Thm_ReweightedNPMLE_positive_iff_exists_nat_mul_ge_one
-- name    : ReweightedNPMLE.positive_iff_exists_nat_mul_ge_one
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:47:36.286257+00:00
-- url     : https://prove2.me/theorems/0814349f-605f-52aa-a1cb-89e3529f4f3c
-- title:
--   Detecting a positive real gap by countably many closed thresholds
-- statement:
--   For every real number $t$,
--   $$t>0\quad\Longleftrightarrow\quad\exists j\in\mathbb N:\ (j+1)t\ge1.$$
--   Equivalently, the positive half-line is the union of the closed threshold sets $[1/(j+1),\infty)$. Applied to a real-valued function, this converts a strict positivity condition into countably many non-strict inequalities, which is useful when closed sets must be projected before establishing measurability.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/CompactOptimizerEvents.lean#L39-L52

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactOptimizerEvents
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Measurable parameterized optimizer events

Continuous optimization on a compact law space has a closed optimizer graph.
Compact projection and countable distance thresholds make failure of
uniqueness and strict optimizer inequalities Borel events. These results are
used to integrate conditional conclusions without assuming a measurable
choice of the conditional good sets.
-/

open Set
open scoped Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.positive_iff_exists_nat_mul_ge_one {t : ℝ} :
    0 < t ↔ ∃ j : ℕ, 1 ≤ ((j : ℝ) + 1) * t := by sorry
