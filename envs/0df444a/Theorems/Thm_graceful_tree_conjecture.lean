-- Prove2me | Theorems.Thm_graceful_tree_conjecture
-- name    : graceful_tree_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T19:39:13.736652+00:00
-- url     : https://prove2.me/theorems/2b0fbab7-83fc-4153-8fc2-25efa378b9ae
-- statement:
--   Graceful tree conjecture (Ringel 1963, Rosa 1967): Every tree with n edges has a graceful labeling: a bijection f from vertices to {0,...,n} where the edge labels |f(u)-f(v)| are all distinct.
-- source:
--   https://en.wikipedia.org/wiki/Graceful_labeling

import Mathlib

import Mathlib

theorem graceful_tree_conjecture (V : Type*) [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) :
    let n := T.edgeFinset.card
    ∃ f : V → Fin (n + 1),
      Function.Injective f ∧
      (T.edgeFinset.image (fun e =>
        max (f e.out.1).val (f e.out.2).val -
        min (f e.out.1).val (f e.out.2).val)).card = n := by
  sorry
