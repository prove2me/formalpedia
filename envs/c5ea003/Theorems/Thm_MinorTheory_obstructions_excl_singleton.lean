-- Prove2me | Theorems.Thm_MinorTheory_obstructions_excl_singleton
-- name    : MinorTheory.obstructions_excl_singleton
-- status  : Disproved
-- author  : @raver1975
-- created : 2026-09-11T16:08:18.416848+00:00
-- url     : https://prove2.me/theorems/437f1847-bb37-45ea-970b-029b20436093
-- title:
--   The obstruction set of a single-excluded-minor class `excl {H}` is exactly
-- statement:
--   The obstruction set of a single-excluded-minor class `excl {H}` is exactly
--   `{H}`.  This identifies the unique minimal forbidden minor.
--
--   ```lean
--   theorem MinorTheory.obstructions_excl_singleton(H : α) :
--       obstructions (excl ({H} : Set α)) = {H} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/OrderFramework.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/OrderFramework.lean#L138

-- Thm stub generated from Novelty/OrderFramework.lean
import Mathlib
import Definitions.Def_Novelty_OrderFramework
/-
  Minor-Closed Graph Classes — Order-Theoretic Framework
  ======================================================

  This file develops the abstract order-theoretic backbone of the theory of
  *minor-closed graph classes*.  We work in a generic ordered type `α` in which
  the relation `x ≤ y` is read as "`x` is a minor of `y`".  Every concrete model
  of the graph-minor relation (or any sub-relation of it, such as the subgraph
  order — see `ForestDensity.lean`) is an instance of this framework.

  A *graph class* is a set `C : Set α`; it is **minor-closed** when it is downward
  closed under the minor relation.  The fundamental construction is `excl S`, the
  class of objects that exclude every member of `S` as a minor.  The key results
  formalise the *easy half of the Robertson–Seymour philosophy*:

  * `excl_minorClosed`              : every excluded-minor class is minor-closed.
  * `minorClosed_excl_obstructions` : conversely, over a well-founded minor order
                                      every minor-closed class is the class of
                                      graphs excluding its set of minimal
                                      obstructions.
  * `obstructions_excl_singleton`   : the obstruction set of a single-excluded-minor
                                      class `excl {H}` is exactly `{H}`.
  * `singleExcludedMinor_iff_obstructions_singleton`
                                    : a minor-closed class is characterised by a
                                      single forbidden minor **iff** its obstruction
                                      set is a singleton.

  The last statement is the abstract form of the mission's target: *being
  characterised by a single forbidden minor* is equivalent to *having a single
  minimal obstruction*.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): "Minor-closed = exclude a set of forbidden minors"
    should be a theorem, not a definition, given well-foundedness of the order.
  Experiment (Experimenter): formalised `excl`, `obstructions`, and proved the
    round trip `MinorClosed C ↔ C = excl (obstructions C)` under `WellFoundedLT`.
  Analysis (Analyst): the forward direction needs only downward closure +
    transitivity; the reverse direction is exactly where well-foundedness enters
    (to extract a *minimal* forbidden minor below any excluded graph).
  Critique (Critic): uniqueness of the obstruction of `excl {H}` genuinely needs
    antisymmetry (`PartialOrder`), not merely a preorder — a preorder allows
    `H ≤ m ≤ H` with `m ≠ H`.  Statement guarded accordingly.
  Synthesis (PI): the single-forbidden-minor property reduces to a singleton
    obstruction set; this is the order-theoretic core of the 3/2 conjecture.
  -- !-- Lab Notes -- !--
-/

open MinorTheory

variable {α : Type*}

variable [Preorder α]














variable [Preorder α] [WellFoundedLT α]




variable [PartialOrder α]

theorem MinorTheory.obstructions_excl_singleton(H : α) :
    obstructions (excl ({H} : Set α)) = {H} := by sorry
