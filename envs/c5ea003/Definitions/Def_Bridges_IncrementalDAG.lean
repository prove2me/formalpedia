-- Prove2me | Definitions.Def_Bridges_IncrementalDAG
-- name    : Bridges_IncrementalDAG
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T09:48:39.987296+00:00
-- url     : https://prove2.me/theorems/7a406164-7ada-4e10-9715-b5d5a82beb0c
-- title:
--   Aether Catalog definitions — Bridges_IncrementalDAG
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.IncrementalDAG`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/IncrementalDAG.lean by skeleton subtraction
import Mathlib
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

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- A predecessor function: `pred v` is the set of immediate predecessors of `v`. -/
abbrev PredFn (V : Type*) [DecidableEq V] := V → Finset V

/-- The relation `u ≺ v` iff `u ∈ pred v` (u is a predecessor of v). -/
def predRel (pred : PredFn V) (u v : V) : Prop := u ∈ pred v

instance (pred : PredFn V) : DecidableRel (predRel pred) :=
  fun u v => Finset.decidableMem u (pred v)

/-- A predecessor function is acyclic if the predecessor relation is well-founded. -/
def DAGAcyclic (pred : PredFn V) : Prop :=
  WellFounded (predRel pred)

/-- The level of a vertex: 0 if it has no predecessors, otherwise
    1 + max over predecessor levels. Defined by well-founded recursion on
    the acyclic predecessor relation. -/
noncomputable def level (pred : PredFn V) (hacyc : DAGAcyclic pred) : V → ℕ :=
  hacyc.fix (fun v ih =>
    if h : (pred v).Nonempty then
      ((pred v).attach).sup' (h.attach) (fun u => ih u.1 u.2 + 1)
    else 0)


/-- Reachability: `Reaches pred u v` means there is a directed path from `u` to `v`
    following edges forward (predecessor → successor direction). -/
inductive Reaches (pred : PredFn V) : V → V → Prop
  | refl (v : V) : Reaches pred v v
  | step {u w v : V} : Reaches pred u w → w ∈ pred v → Reaches pred u v


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

/-
**Support theorem**: The set of vertices whose level changes is contained
    in the forward reachability cone of the new node. This is the theorem that
    says: the recomputation set is contained in the forward dependency cone.
-/

/-! ## Level characterization -/

/-
The level of a source (no predecessors) is 0.
-/

/-
The level is always at least `level u + 1` for any predecessor `u`.
-/

/-
Level is monotone along edges: if `u ∈ pred v` then `level u < level v`.
-/

/-
The complement of the forward cone is the maximal region where levels
    are guaranteed unchanged by any localized update.
-/


