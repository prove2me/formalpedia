-- Prove2me | Theorems.Thm_triangle_free_chromatic_number
-- name    : triangle_free_chromatic_number
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T01:50:38.06166+00:00
-- url     : https://prove2.me/theorems/01e120c9-deba-4d52-9678-7db066cf2eff
-- statement:
--   Triangle-free graphs with large chromatic number: For any k, triangle-free graphs with χ(G) ≥ k exist. Mycielski (1955) gave an explicit construction. Shows independence number and chromatic number are independent parameters.
-- source:
--   https://en.wikipedia.org/wiki/Triangle-free_graph

import Mathlib

import Mathlib

theorem triangle_free_chromatic_number :
    ∀ k : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (hD : DecidableRel G.Adj),
      @SimpleGraph.chromaticNumber (Fin n) G ≥ k ∧
      ¬∃ a b c : Fin n, G.Adj a b ∧ G.Adj b c ∧ G.Adj a c := by
  sorry
