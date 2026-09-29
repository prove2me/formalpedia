-- Prove2me | Theorems.Thm_level_eq_of_not_reaches
-- name    : level_eq_of_not_reaches
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T10:43:48.578784+00:00
-- url     : https://prove2.me/theorems/8bcd1b23-0782-401c-8111-7214726cc98c
-- title:
--   Level eq of not reaches
-- statement:
--   Formal statement of `level_eq_of_not_reaches` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem level_eq_of_not_reaches    (predOld predNew : PredFn V)
--       (new : V)
--       (hacycOld : DAGAcyclic predOld) (hacycNew : DAGAcyclic predNew)
--       (hlocal : ∀ v, ¬ Reaches predNew new v → predOld v = predNew v)
--       (v : V)
--       (hv : ¬ Reaches predNew new v) :
--       level predOld hacycOld v = level predNew hacycNew v := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/IncrementalDAG.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/IncrementalDAG.lean#L87

-- Thm stub generated from Bridges/IncrementalDAG.lean
import Mathlib
import Definitions.Def_Bridges_IncrementalDAG
/-
# Incremental Recomputation on Dependency DAGs

A certified locality theorem: when a new node is inserted into a finite DAG,
the recursively defined "level" (longest incoming path length) changes only
within the forward reachability cone of the new node.

## Main results

* `level_eq_of_not_reaches` — levels are unchanged outside the forward cone
* `recomputation_support_subset_forward_cone` — the set of changed vertices
  is contained in the forward cone
-/

-- open removed: section is not a namespace

variable {V : Type*} [DecidableEq V] [Fintype V]









/-! ## Main locality theorem -/

/-
**Key locality lemma**: If `predOld v = predNew v` and the levels of all
    predecessors of `v` agree between old and new, then `level v` also agrees.
-/

/-
**Main theorem**: If `v` is not reachable from `new` in the new graph,
    and the predecessor function is unchanged outside the forward cone of `new`,
    then the level of `v` is unchanged.

    This formalizes the principle that incremental recomputation after inserting
    a new node into a dependency DAG need only visit the forward cone of
    that node.
-/

theorem level_eq_of_not_reaches    (predOld predNew : PredFn V)
    (new : V)
    (hacycOld : DAGAcyclic predOld) (hacycNew : DAGAcyclic predNew)
    (hlocal : ∀ v, ¬ Reaches predNew new v → predOld v = predNew v)
    (v : V)
    (hv : ¬ Reaches predNew new v) :
    level predOld hacycOld v = level predNew hacycNew v := by sorry
