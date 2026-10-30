-- Prove2me | Theorems.Thm_gpy_fiberCountSelberg_le
-- name    : gpy_fiberCountSelberg_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T20:25:55.81324+00:00
-- url     : https://prove2.me/theorems/b2655a46-412c-4edb-b303-2edfcb0bf799
-- title:
--   Selberg fiber count at L is at most tau_{k+1}(L)^2
-- statement:
--   The number of Selberg support pairs, good at a coordinate i, with combined modulus L and both products squarefree, is at most tau_{k+1}(L)^2: each side's product divides L, so the fiber sits inside a product of one-sided divisor fibers, each bounded by tau_{k+1}(L). The squarefree restriction is essential.
-- source:
--   GPY Selberg fiber bound for tuple weights, formalized from Mathlib (squarefree products, pairwise coprimality, and fiber counting)

import Mathlib
open Classical

theorem gpy_fiberCountSelberg_le {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (i : Fin k) (L : ℕ) :
    ((((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)) ×ˢ
        ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R))).filter
      (fun p : (Fin k → ℕ) × (Fin k → ℕ) => (∃ w, (∀ j, Nat.lcm (p.1 j) (p.2 j) ∣ w + h j) ∧
          Nat.Coprime (w + h i)
            (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)))) ∧
        Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L ∧
        Squarefree (∏ j, p.1 j) ∧ Squarefree (∏ j, p.2 j))).card
      ≤ ((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
        (fun d => ∏ i, d i = L)).card ^ 2 := by sorry
