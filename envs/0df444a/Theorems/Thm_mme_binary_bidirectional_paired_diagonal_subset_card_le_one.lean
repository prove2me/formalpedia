-- Prove2me | Theorems.Thm_mme_binary_bidirectional_paired_diagonal_subset_card_le_one
-- name    : mme_binary_bidirectional_paired_diagonal_subset_card_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T12:22:05.165642+00:00
-- url     : https://prove2.me/theorems/dc452c5d-9541-455a-9412-6d690086dd7c
-- title:
--   Bidirectional binary paired conflicts tensor to a complete obstruction
-- statement:
--   Let a ternary relation on $\{0,1\}$ contain $(0,0,0),(0,0,1),(1,1,0),(1,1,1)$. In its $k$-fold coordinate product, $(u,u,v)$ is supported for every two binary words $u,v$. Therefore every subset on which such support forces $u=v$ has cardinality at most one. This records why bidirectional paired conflicts can make post-hoc diagonal extraction exponentially lossy.
-- source:
--   Elementary coordinate-product obstruction arising in the paired cyclic 121/211 analysis of the Coppersmith-Winograd tensor square.

import Mathlib.Data.Finset.Card

set_option autoImplicit false

theorem mme_binary_bidirectional_paired_diagonal_subset_card_le_one
    (R : Fin 2 → Fin 2 → Fin 2 → Prop)
    (h000 : R 0 0 0) (h001 : R 0 0 1)
    (h110 : R 1 1 0) (h111 : R 1 1 1)
    (k : ℕ) (P : Finset (Fin k → Fin 2))
    (hDiagonal : ∀ u ∈ P, ∀ v ∈ P,
      (∀ i, R (u i) (u i) (v i)) → u = v) :
    P.card ≤ 1 := by
  sorry
