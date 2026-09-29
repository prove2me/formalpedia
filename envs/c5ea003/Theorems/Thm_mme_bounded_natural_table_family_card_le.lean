-- Prove2me | Theorems.Thm_mme_bounded_natural_table_family_card_le
-- name    : mme_bounded_natural_table_family_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:51:59.397437+00:00
-- url     : https://prove2.me/theorems/19201043-9b8f-4035-8146-c35d380e1702
-- title:
--   A bounded $k$-cell table family has at most $(N+1)^k$ members
-- statement:
--   Let $I$ be a finite index set and let $T$ be a finite family of natural-number tables $a:I\to\mathbb N$.  If every cell of every table is at most $N$, then
--
--   $$
--   |T|\le (N+1)^{|I|}.
--   $$
--
--   Indeed, every table is an element of the full function space $I\to\{0,1,\dots,N\}$.  For the fifteen supported joint types in the Coppersmith--Winograd profile calculation, this yields the exact polynomial table-count factor $(N+1)^{15}$.
-- source:
--   Elementary finite counting; used in the dominant-profile completion bound of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib

theorem mme_bounded_natural_table_family_card_le
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : Finset (ι → ℕ)) (N : ℕ)
    (hbound : ∀ a ∈ T, ∀ i, a i ≤ N) :
    T.card ≤ (N + 1) ^ Fintype.card ι := by
  sorry
