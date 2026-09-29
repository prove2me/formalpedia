-- Prove2me | Theorems.Thm_mme_dwz_square112_row_injective
-- name    : mme_dwz_square112_row_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-08T08:17:21.510581+00:00
-- url     : https://prove2.me/theorems/8c4280ad-da36-4ba6-87db-82656c0f74b8
-- title:
--   Square112 fine rows are pairwise distinct
-- statement:
--   The canonical CW-square112 component has four literal left fine split rows, listed in the released consumer order as (0,0,2), (0,1,1), (1,0,1), (1,1,0). These four grade triples are pairwise distinct, so the map sending a row index to the triple of grades it presents to the three tensor modes is injective.
--
--   Equivalently, a fine row is recoverable from the grades it shows the three modes. This is the elementary input to the vertex-map half of the three-cyclic incidence certificate: it is what lets a mode-indexed triple of grade words be read back as a single word in the four rows.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173v5, Section 7.2 (printed p. 66) and Equation (34) (p. 71), https://arxiv.org/abs/2210.10173v5

import Definitions.Def_mme_dwz_square112_exact_profile_data

open MME.DWZSquare112

set_option autoImplicit false

theorem mme_dwz_square112_row_injective : Function.Injective row := by sorry
