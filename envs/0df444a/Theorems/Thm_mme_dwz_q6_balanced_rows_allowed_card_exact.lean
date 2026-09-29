-- Prove2me | Theorems.Thm_mme_dwz_q6_balanced_rows_allowed_card_exact
-- name    : mme_dwz_q6_balanced_rows_allowed_card_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:27:45.80338+00:00
-- url     : https://prove2.me/theorems/8ab453bf-a434-4cc1-967a-07e35500cd73
-- title:
--   Exact available-word count for the four balanced q=6 Table-2 rows
-- statement:
--   For any Table-2 scale $m$ and any balanced rectangular row $s\in\{3,4,5,7\}$, let $N$ be the row multiplicity and let $k$ be either of its two equal nonzero split multiplicities. The number $D_s(m)$ of literal canonical $Z$-words satisfying Definition 5.4 is exactly
--
--   $$
--   D_s(m)=\#\{g\in\{0,1\}^N:\#g^{-1}(0)=\#g^{-1}(1)=k\}\,6^N.
--   $$
--
--   The binary word selects which of the two fine split grades occurs at every position, while the factor $6^N$ selects the independent channel within each split grade. The formula applies uniformly to rows $013$, $031$, $103$, and $301$ in their Table-2 ordering.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.4 and Section 6.3/Table 2, rows 013, 031, 103, and 301.

import Definitions.Def_mme_dwz_component_word_projection
import Theorems.Thm_mme_dwz_q6_balanced_rectangular_product_coordinates
import Theorems.Thm_mme_prescribed_product_alphabet_word_card

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_balanced_rows_allowed_card_exact
    (m : ℕ) (s : Fin 15) (hs : s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 7) :
    let k := MME.DWZTable2Counts.split s 1 * m
    let N := MME.DWZTable2Counts.component s * m
    Nat.card
        {w : PowIndex (LiftedCoarsePair.{u} 6 (MME.DWZSquare.shapeZ s)) N //
          componentWordAllowed s m w} =
      Nat.card
          {g : Fin N → Fin 2 //
            ∀ h, Fintype.card {r : Fin N // g r = h} = k} *
        6 ^ N := by
  sorry
