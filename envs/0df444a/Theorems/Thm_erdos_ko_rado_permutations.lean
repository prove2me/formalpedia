-- Prove2me | Theorems.Thm_erdos_ko_rado_permutations
-- name    : erdos_ko_rado_permutations
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-31T21:05:12.607529+00:00
-- url     : https://prove2.me/theorems/d3f557e2-27d6-4e5b-9352-a171f5b5c4f7
-- statement:
--   Erdős–Ko–Rado for permutations: An intersecting family of permutations of {1,...,n} has size at most (n-1)!. Proved by Deza–Frankl (1983). The analogous result for t-intersecting families with sharper bounds is still studied.
-- source:
--   https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Ko%E2%80%93Rado_theorem

import Mathlib

import Mathlib

theorem erdos_ko_rado_permutations (n : ℕ) (hn : 2 ≤ n)
    (F : Finset (Equiv.Perm (Fin n)))
    (hint : ∀ sigma ∈ F, ∀ tau ∈ F, ∃ i : Fin n, sigma i = tau i) :
    F.card ≤ (n - 1).factorial := by
  sorry
