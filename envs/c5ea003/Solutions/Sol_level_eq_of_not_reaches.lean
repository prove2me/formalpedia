-- Prove2me | solution 1 for level_eq_of_not_reaches
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T07:47:42.277368+00:00
-- url     : https://prove2.me/submissions/a7c1e2e1-7281-493b-92c6-f07e7e9f06d6

import Mathlib
import Definitions.Def_Bridges_IncrementalDAG

set_option maxHeartbeats 2000000
set_option autoImplicit false

-- ==== upstream: Packages/Catalog/Bridges/IncrementalDAG.lean ====
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

-- [dropped: platform already declares PredFn]
-- [dropped: platform already declares predRel]
-- [dropped: platform already declares DAGAcyclic]
-- [dropped: platform already declares level]
/-- Unfolding lemma for `level`. -/
theorem level_unfold (pred : PredFn V) (hacyc : DAGAcyclic pred) (v : V) :
    level pred hacyc v =
      if h : (pred v).Nonempty then
        ((pred v).attach).sup' (h.attach) (fun u => level pred hacyc u.1 + 1)
      else 0 := by
  unfold level
  rw [WellFounded.fix_eq]

-- [dropped: platform already declares Reaches]
theorem Reaches.trans {pred : PredFn V} {u v w : V}
    (h1 : Reaches pred u v) (h2 : Reaches pred v w) : Reaches pred u w := by
  induction h2
  case refl => exact h1
  case step x y z ha hb ih => exact Reaches.step ih hb

/-! ## Main locality theorem -/

/-
**Key locality lemma**: If `predOld v = predNew v` and the levels of all
    predecessors of `v` agree between old and new, then `level v` also agrees.
-/
theorem level_eq_of_pred_eq_and_levels_eq
    (predOld predNew : PredFn V)
    (hacycOld : DAGAcyclic predOld) (hacycNew : DAGAcyclic predNew)
    (v : V)
    (hpred : predOld v = predNew v)
    (hlevels : ∀ u ∈ predOld v, level predOld hacycOld u = level predNew hacycNew u) :
    level predOld hacycOld v = level predNew hacycNew v := by
  rw [ level_unfold, level_unfold, hpred ];
  grind

/-
**Main theorem**: If `v` is not reachable from `new` in the new graph,
    and the predecessor function is unchanged outside the forward cone of `new`,
    then the level of `v` is unchanged.

    This formalizes the principle that incremental recomputation after inserting
    a new node into a dependency DAG need only visit the forward cone of
    that node.
-/
theorem solution
    (predOld predNew : PredFn V)
    (new : V)
    (hacycOld : DAGAcyclic predOld) (hacycNew : DAGAcyclic predNew)
    (hlocal : ∀ v, ¬ Reaches predNew new v → predOld v = predNew v)
    (v : V)
    (hv : ¬ Reaches predNew new v) :
    level predOld hacycOld v = level predNew hacycNew v := by
  -- Apply well-founded induction on the new predecessor relation.
  have h_ind : ∀ v, ¬Reaches predNew new v → ∀ u, Reaches predNew u v → ¬Reaches predNew new u := by
    intro v hv u hu huv
    have h_contra : Reaches predNew new v := by
      exact Reaches.trans huv hu
    contradiction;
  have h_ind : ∀ v, ¬Reaches predNew new v → level predOld hacycOld v = level predNew hacycNew v := by
    intro v hv
    induction' v using hacycNew.induction with v ih;
    apply level_eq_of_pred_eq_and_levels_eq predOld predNew hacycOld hacycNew v (hlocal v hv);
    intro u hu;
    apply ih u;
    · unfold predRel; specialize hlocal v hv; aesop;
    · apply h_ind v hv u;
      exact Reaches.step (Reaches.refl u) ( hlocal v hv ▸ hu );
  exact h_ind v hv


#print axioms solution
