-- Prove2me | solution 1 for mme_CW_section7_balanced_block_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-23T23:09:36.895626+00:00
-- url     : https://prove2.me/submissions/09e828e8-caea-4bb4-b44e-862c2ea10473

import Theorems.Thm_mme_CW_type_sequence_restrict

open MME BigOperators

universe u

/-!
The exact six-type profile used in CW90 Section 7: each boundary type occurs
`L` times and each middle type occurs `N-L` times in a sequence of length
`3N`.  Only the middle counts affect the three MM dimensions, while the full
profile is retained because it is the input to the later pruning count.
-/

theorem solution
    {K : Type u} [Field K] (q N L : ℕ) (hL : L ≤ N)
    (τ : Fin (3 * N) → Fin 3 × Fin 3 × Fin 3)
    (hτ : ∀ k : Fin (3 * N), τ k ∈ CWSupportPattern)
    (h200 :
      (Finset.univ.filter (fun k : Fin (3 * N) => τ k = (2, 0, 0))).card = L)
    (h020 :
      (Finset.univ.filter (fun k : Fin (3 * N) => τ k = (0, 2, 0))).card = L)
    (h002 :
      (Finset.univ.filter (fun k : Fin (3 * N) => τ k = (0, 0, 2))).card = L)
    (h101 :
      (Finset.univ.filter (fun k : Fin (3 * N) => τ k = (1, 0, 1))).card = N - L)
    (h110 :
      (Finset.univ.filter (fun k : Fin (3 * N) => τ k = (1, 1, 0))).card = N - L)
    (h011 :
      (Finset.univ.filter (fun k : Fin (3 * N) => τ k = (0, 1, 1))).card = N - L) :
    TensorObj.Restrict
      (MMObj K (q ^ (N - L)) (q ^ (N - L)) (q ^ (N - L)))
      ((CWObj K q).kronPow (3 * N)) := by
  have h := mme_CW_type_sequence_restrict (K := K) q (3 * N) τ hτ
  rw [h101, h110, h011] at h
  exact h
