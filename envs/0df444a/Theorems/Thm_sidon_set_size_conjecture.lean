-- Prove2me | Theorems.Thm_sidon_set_size_conjecture
-- name    : sidon_set_size_conjecture
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T02:59:50.484714+00:00
-- url     : https://prove2.me/theorems/be510201-64e9-41d4-b9fe-7f8b62497a51
-- statement:
--   Sidon set (B₂ set) size: Maximum size of a set S ⊆ {1,...,n} with all pairwise sums distinct is ≤ (1+o(1))√n. The Erdős-Turán conjecture says the max is √n + O(n^{1/4}). Best construction gives ~0.998√n. Exact constant unknown.
-- source:
--   https://en.wikipedia.org/wiki/Sidon_set

import Mathlib

import Mathlib

theorem sidon_set_size_conjecture :
    ∀ eps : ℝ, 0 < eps →
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (S : Finset (Fin n)),
      (∀ a b c d : Fin n, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
        a ≠ b → (a.val + b.val = c.val + d.val) → ({a,b} : Finset (Fin n)) = {c,d}) →
      (S.card : ℝ) ≤ C * Real.sqrt n * (1 + eps) := by
  sorry
