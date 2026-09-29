-- Prove2me | Theorems.Thm_moore_bound_conjecture
-- name    : moore_bound_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:20:36.038006+00:00
-- url     : https://prove2.me/theorems/77a9c415-f930-4e9a-9cf8-5597003bfd92
-- statement:
--   Cage problem (Moore bound): The smallest k-regular graph of girth g has at least 1+k∑_{i=0}^{⌊(g-1)/2⌋-1}(k-1)^i vertices (the Moore bound). Graphs achieving this bound are called Moore graphs or cages. Their existence and uniqueness for most parameters is open.
-- source:
--   https://en.wikipedia.org/wiki/Cage_(graph_theory)

import Mathlib

import Mathlib

theorem moore_bound_conjecture (k g : ℕ) (hk : 3 ≤ k) (hg : 3 ≤ g) (hodd : ¬ 2 ∣ g) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (hD : DecidableRel G.Adj),
      (∀ v : Fin n, G.degree v = k) ∧
      G.girth = g ∧
      n ≤ 1 + k * ∑ i ∈ Finset.range ((g - 1) / 2), (k - 1) ^ i := by
  sorry
