-- Prove2me | Theorems.Thm_erdos_gallai_path_conjecture
-- name    : erdos_gallai_path_conjecture
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-31T19:57:03.41703+00:00
-- url     : https://prove2.me/theorems/3b1b5aec-e99d-41b8-8c25-46d1d738222b
-- statement:
--   Erdős–Gallai theorem on paths (1959): The maximum number of edges in a graph on n vertices with no path of length k+1 is at most (k/2)·n. The tight bound (k-1)n/2 was proved for k≥2; the conjecture asks whether the extremal graphs are well-characterized.
-- source:
--   https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Gallai_theorem

import Mathlib

import Mathlib

-- Erdős–Gallai conjecture on path-extremal graphs:
-- ex(n; P_{k+1}) ≤ k/2 * n for every k ≥ 1
-- where ex(n; P_{k+1}) = max edges in n-vertex graph with no path of length k+1
-- (Currently proved: ex(n; P_{k+1}) ≤ (k-1)/2 * n, Erdős-Gallai 1959)
theorem erdos_gallai_path_conjecture (n k : ℕ) (hk : 1 ≤ k) :
    ∀ G : SimpleGraph (Fin n), [DecidableRel G.Adj] →
      (¬∃ path : Fin (k + 2) → Fin n, Function.Injective path ∧
        ∀ i : Fin (k + 1), G.Adj (path i.castSucc) (path i.succ)) →
      2 * G.edgeFinset.card ≤ k * n := by
  sorry
