-- Prove2me | Theorems.Thm_mme_dwz_q6_row9_component_allowed_card_eq_restricted022
-- name    : mme_dwz_q6_row9_component_allowed_card_eq_restricted022
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T07:24:41.504871+00:00
-- url     : https://prove2.me/theorems/3cafa82a-c81a-48cc-b046-8ccc13c96c6e
-- title:
--   Exact cardinality bridge for the q=6 row-9 restricted words
-- statement:
--   At every integral scaling factor $m$, the canonical row-$9$ component-word predicate selects exactly as many coarse words as the explicit restricted $022$ word type at the Table-2 parameters. Writing $A_m$ for the allowed component words and $R_m$ for the restricted words,
--
--   $$
--   |A_m|=|R_m|.
--   $$
--
--   This identifies the coordinate set retained by the row-$9$ tensor projector with the exact matrix-multiplication dimension used in the Table-2 extraction, without an asymptotic approximation.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Lemma 4.6 and the exact 022 word counts used in Table 2.

import Definitions.Def_mme_dwz_table2_component_022_word_data
import Definitions.Def_mme_dwz_component_word_projection

open MME MME.DWZComponentRestriction
open MME.DWZTable2Component022

universe u

set_option autoImplicit false

theorem mme_dwz_q6_row9_component_allowed_card_eq_restricted022
    (m : ℕ) :
    Nat.card {w : PowIndex (LiftedCoarsePair.{u} 6 2)
        (MME.DWZTable2Counts.component 9 * m) //
      componentWordAllowed (9 : Fin 15) m w} =
      Nat.card (Restricted022Word 6
        (table2Power022 (10366945 * m))
        (table2OuterCount022 (10366945 * m))
        (table2MiddleCount022 (10366945 * m))) := by
  sorry
