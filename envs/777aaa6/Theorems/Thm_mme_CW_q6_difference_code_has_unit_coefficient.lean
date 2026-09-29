-- Prove2me | Theorems.Thm_mme_CW_q6_difference_code_has_unit_coefficient
-- name    : mme_CW_q6_difference_code_has_unit_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:22:17.921955+00:00
-- url     : https://prove2.me/theorems/1748d3e5-8974-430c-a350-d2fb0119db18
-- title:
--   Every positive-middle q=6 address has a unit hash coefficient
-- statement:
--   Let an exact coupled q=6 address have positive middle parameter $G$. Its Z-word has exactly $2G>0$ coordinates of grade $2$. At any such coordinate, q=6 support forces the X-minus-Z doubled-hash coefficient to be $+1$ or $-1$. Therefore the coefficient word has a unit entry over every residue ring.
--
--   This is the single-event nondegeneracy input for exact affine-hash fiber counting in the fixed-Z first and second moments.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), q=6 first-hash profile and the 2G oriented middle coordinates on journal pp. 270--271

import Mathlib
import Definitions.Def_mme_CW_q6_doubled_hash_arithmetic

open MME

set_option autoImplicit false

theorem mme_CW_q6_difference_code_has_unit_coefficient
    {M N L G : ℕ} [NeZero M]
    (e : CWQ6ExactCoupledAddress N L G)
    (hG : 0 < G) :
    ∃ j : Fin (2 * N), IsUnit (
      (2 * ((e.1 0 j).val : ZMod M)) -
        (cwQ6CoupledZHashCode (e.1 2 j) : ZMod M)) := by
  sorry
