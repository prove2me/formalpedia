-- Prove2me | Theorems.Thm_graceful_tree_conjecture_v2
-- name    : graceful_tree_conjecture_v2
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:53:30.280717+00:00
-- url     : https://prove2.me/theorems/ac8abd6a-7317-4b21-8cf3-131a4c262349
-- statement:
--   Graceful tree conjecture (Ringel 1963, Rosa 1967): Every tree has a graceful labeling. Verified for all trees up to 35 vertices. Open in general.
-- source:
--   https://en.wikipedia.org/wiki/Graceful_labeling

import Mathlib

import Mathlib

theorem graceful_tree_conjecture_v2 (V : Type*) [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) :
    ∃ (f : V → Fin (T.edgeFinset.card + 1)),
      Function.Injective f ∧
      (T.edgeFinset.image (fun e =>
        let v := e.out; max (f v.1).val (f v.2).val - min (f v.1).val (f v.2).val)).card =
      T.edgeFinset.card := by
  sorry
