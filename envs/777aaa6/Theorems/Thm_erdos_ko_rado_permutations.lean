-- Prove2me | Theorems.Thm_erdos_ko_rado_permutations
-- name    : erdos_ko_rado_permutations
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-31T21:05:12.607529+00:00
-- url     : https://prove2.me/theorems/658e6b80-933a-46f0-95ea-c66829b1bbc4
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
