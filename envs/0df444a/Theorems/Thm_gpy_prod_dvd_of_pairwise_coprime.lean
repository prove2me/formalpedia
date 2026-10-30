-- Prove2me | Theorems.Thm_gpy_prod_dvd_of_pairwise_coprime
-- name    : gpy_prod_dvd_of_pairwise_coprime
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T20:25:52.207649+00:00
-- url     : https://prove2.me/theorems/ad422887-ddb4-4f9a-8ed8-e7159a8c122f
-- title:
--   A pairwise-coprime family divides a common multiple
-- statement:
--   If a family of integers is pairwise coprime and every coordinate divides L, then the product of the family divides L, by induction on the tuple dimension.
-- source:
--   GPY Selberg fiber bound for tuple weights, formalized from Mathlib (squarefree products, pairwise coprimality, and fiber counting)

import Mathlib
open Classical

theorem gpy_prod_dvd_of_pairwise_coprime :
    ∀ {k : ℕ} {d : Fin k → ℕ} {L : ℕ},
      (∀ i j, i ≠ j → Nat.Coprime (d i) (d j)) →
      (∀ i, d i ∣ L) → ∏ i, d i ∣ L := by sorry
