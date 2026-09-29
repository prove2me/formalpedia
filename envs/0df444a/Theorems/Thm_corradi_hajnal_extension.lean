-- Prove2me | Theorems.Thm_corradi_hajnal_extension
-- name    : corradi_hajnal_extension
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:28:42.308862+00:00
-- url     : https://prove2.me/theorems/2e0b7928-57c3-417a-89c0-f5b6e32ed690
-- statement:
--   Corrádi–Hajnal theorem: Any graph on n ≥ 3k vertices with minimum degree ≥ 2k contains k vertex-disjoint cycles. Proved by Corrádi–Hajnal (1963). Extensions to vertex-disjoint paths, prescribed lengths, and digraph versions are open.
-- source:
--   https://en.wikipedia.org/wiki/Corr%C3%A1di%E2%80%93Hajnal_theorem

import Mathlib

import Mathlib

theorem corradi_hajnal_extension (n k : ℕ) (hn : 3 * k ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hmin : ∀ v : Fin n, 2 * k ≤ G.degree v) :
    ∃ (cycles : Fin k → Finset (Fin n)),
      (∀ i, 3 ≤ (cycles i).card) ∧
      (∀ i j : Fin k, i ≠ j → Disjoint (cycles i) (cycles j)) ∧
      ∀ i, ∃ f : ZMod (cycles i).card → (cycles i),
        Function.Bijective f ∧
        ∀ j : ZMod (cycles i).card,
          G.Adj (f j : Fin n) (f (j + 1) : Fin n) := by
  sorry
