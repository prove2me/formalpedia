-- Prove2me | Theorems.Thm_mme_bounded_natural_table_family_card_le
-- name    : mme_bounded_natural_table_family_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T23:29:32.447269+00:00
-- url     : https://prove2.me/theorems/e778ea8f-0435-4aeb-afa5-b16a7219568a
-- title:
--   A bounded finite table family has at most the full box cardinality
-- statement:
--   Let $I$ be a finite index set and let $T$ be a finite family of natural-number tables $a:I\to\mathbb N$. If every entry of every table is at most $N$, then
--
--   $$
--   |T|\le (N+1)^{|I|}.
--   $$
--
--   For the fifteen supported joint types in the Coppersmith--Winograd profile calculation, this gives the polynomial table-count factor $(N+1)^{15}$.
-- source:
--   Elementary finite counting; used in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib

open BigOperators

set_option autoImplicit false

theorem mme_bounded_natural_table_family_card_le
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : Finset (ι → ℕ)) (N : ℕ)
    (hbound : ∀ a ∈ T, ∀ i, a i ≤ N) :
    T.card ≤ (N + 1) ^ Fintype.card ι := by
  sorry
