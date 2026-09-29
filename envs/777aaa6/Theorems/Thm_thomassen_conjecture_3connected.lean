-- Prove2me | Theorems.Thm_thomassen_conjecture_3connected
-- name    : thomassen_conjecture_3connected
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-31T21:14:01.99361+00:00
-- url     : https://prove2.me/theorems/a5f97246-9113-4c01-8869-26cbf1ffa085
-- statement:
--   Thomassen's conjecture (1982): Every 3-connected graph has a cycle through any 3 prescribed vertices. Proved for planar graphs; the general case is equivalent to asking whether 3-connectedness implies certain Hamiltonian path structures. Open for non-planar graphs.
-- source:
--   https://en.wikipedia.org/wiki/Thomassen%27s_conjecture

import Mathlib

import Mathlib

theorem thomassen_conjecture_3connected (n : ℕ) (hn : 4 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3conn : ∀ S : Finset (Fin n), S.card ≤ 2 →
      (G.induce (Set.univ \ S.toSet)).Connected)
    (v1 v2 v3 : Fin n) (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3) :
    ∃ (m : ℕ) (f : ZMod m → Fin n),
      Function.Injective f ∧
      4 ≤ m ∧
      (∃ i, f i = v1) ∧ (∃ j, f j = v2) ∧ (∃ k, f k = v3) ∧
      ∀ i : ZMod m, G.Adj (f i) (f (i + 1)) := by
  sorry
