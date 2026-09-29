-- Prove2me | Theorems.Thm_mme_dwz_square112_modeWord_jointly_injective
-- name    : mme_dwz_square112_modeWord_jointly_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-08T08:17:20.196839+00:00
-- url     : https://prove2.me/theorems/9fc8f3df-f4d5-4f95-b04c-a1e16e2f4071
-- title:
--   Mode words jointly determine a square112 exact word
-- statement:
--   Fix a length `N` and prescribed row multiplicities `c`. Each exact word `w` in the four square112 split rows induces, for every tensor mode `i`, a mode word recording the grade that mode sees at each position.
--
--   The three mode maps are **jointly** injective: if two exact words induce the same triple of mode words, they are equal. This is the vertex-map component of the three-cyclic incidence certificate — the incidence assigning to each exact word its triple of mode vertices is injective, so hyperedges are not collapsed.
--
--   It follows pointwise from distinctness of the four literal rows; no counting or extraction conclusion is used.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173v5, Section 7.2 (printed p. 66) and Equation (34) (p. 71), https://arxiv.org/abs/2210.10173v5

import Definitions.Def_mme_dwz_square112_exact_profile_data

open MME.DWZSquare112

set_option autoImplicit false

theorem mme_dwz_square112_modeWord_jointly_injective (N : ℕ) (c : Fin 4 → ℕ) :
    Function.Injective
      (fun w : ExactWord N c => (fun i => modeWord w i : Fin 3 → Fin N → Fin 3)) := by sorry
