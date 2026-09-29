-- Prove2me | Theorems.Thm_hadwiger_conjecture
-- name    : hadwiger_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T19:34:00.82683+00:00
-- url     : https://prove2.me/theorems/ccc12de1-72d3-444b-b955-cc774e0367e6
-- statement:
--   Hadwiger's conjecture (1943): Every graph with chromatic number ≥ k contains K_k as a minor (k disjoint connected subgraphs pairwise joined by an edge). The cases k ≤ 6 are proved; k = 7 and beyond remain open.
-- source:
--   https://en.wikipedia.org/wiki/Hadwiger_conjecture_(graph_theory)

import Mathlib

import Mathlib

theorem hadwiger_conjecture (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k)
    (hcolor : ¬G.Colorable (k - 1)) :
    ∃ (parts : Fin k → Set V),
      (∀ i, (G.induce (parts i)).Connected) ∧
      (∀ i j, i ≠ j → Disjoint (parts i) (parts j)) ∧
      (∀ i j, i ≠ j → ∃ v ∈ parts i, ∃ w ∈ parts j, G.Adj v w) := by
  sorry
