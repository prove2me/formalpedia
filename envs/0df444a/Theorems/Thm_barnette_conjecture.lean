-- Prove2me | Theorems.Thm_barnette_conjecture
-- name    : barnette_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T19:49:52.250713+00:00
-- url     : https://prove2.me/theorems/27c3b45a-5800-4bfb-a979-b9dac9b098d6
-- statement:
--   Barnette's conjecture (1969): Every 3-connected bipartite cubic planar graph has a Hamiltonian cycle. Reduced to: every 3-connected bipartite cubic graph with a Hamiltonian path has a Hamiltonian cycle.
-- source:
--   https://en.wikipedia.org/wiki/Barnette%27s_conjecture

import Mathlib

import Mathlib

-- Barnette conjecture: every 3-connected bipartite cubic planar graph has a Hamiltonian cycle
-- Cubic: all degrees = 3; Bipartite: 2-colorable; 3-connected: remove any 2 vertices → connected
theorem barnette_conjecture (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbipartite : G.IsBipartite)
    (h3conn : ∀ S : Finset V, S.card ≤ 2 → (G.induce (Set.univ \ (S : Set V))).Connected) :
    ∃ f : ZMod (Fintype.card V) → V,
      Function.Bijective f ∧
      ∀ i : ZMod (Fintype.card V), G.Adj (f i) (f (i + 1)) := by
  sorry
