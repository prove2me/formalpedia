-- Prove2me | Theorems.Thm_erdos_szekeres_conjecture
-- name    : erdos_szekeres_conjecture
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-05-31T20:25:41.077633+00:00
-- url     : https://prove2.me/theorems/05240ef7-3622-41cc-8b9e-4156b91eaada
-- statement:
--   The Erdős–Szekeres conjecture (1935): ES(k) = 2^{k−2} + 1, i.e., any set of 2^{k-2}+1 points in general position in ℝ² contains k points in convex position, and this is tight. Proved for k ≤ 6 (the k=4 case is the 'happy ending'); the exact value 2^{k-2}+1 for k ≥ 7 is open.
-- source:
--   https://en.wikipedia.org/wiki/Happy_ending_problem

import Mathlib

import Mathlib

theorem erdos_szekeres_conjecture (k : ℕ) (hk : 3 ≤ k) :
    ∃ (N : ℕ) (_ : N = 2 ^ (k - 2) + 1),
    ∀ (pts : Fin N → ℝ × ℝ),
      Function.Injective pts →
      (∀ i j m : Fin N, i ≠ j → j ≠ m → i ≠ m →
        ¬ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
          pts m = ((pts i).1 + t * ((pts j).1 - (pts i).1),
                   (pts i).2 + t * ((pts j).2 - (pts i).2))) →
      ∃ (S : Finset (Fin N)) (_ : S.card = k),
        ∀ i ∈ S, ∀ j ∈ S, ∀ m ∈ S,
          i ≠ j → j ≠ m → i ≠ m →
          ¬ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
            pts m = ((pts i).1 + t * ((pts j).1 - (pts i).1),
                     (pts i).2 + t * ((pts j).2 - (pts i).2)) → False := by
  sorry
