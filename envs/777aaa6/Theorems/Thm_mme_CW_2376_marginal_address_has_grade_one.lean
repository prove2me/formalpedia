-- Prove2me | Theorems.Thm_mme_CW_2376_marginal_address_has_grade_one
-- name    : mme_CW_2376_marginal_address_has_grade_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:35:59.619983+00:00
-- url     : https://prove2.me/theorems/0f753478-e4e0-441f-b414-8fa9e7f85511
-- title:
--   Every positive-scale CW marginal word has a grade-one coordinate
-- statement:
--   At every positive CW scale, each of the three mode words of a marginal-supported address contains at least one coordinate of grade one.
--
--   Indeed, the prescribed grade-one marginal multiplicity is $1,308,290m$, which is positive. This supplies a unit coefficient in the modular linear hash and enables exact prime-field fiber counting.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), optimized marginal profile on journal pp. 267--268; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_marginal_support_hypergraph

open MME

theorem mme_CW_2376_marginal_address_has_grade_one
    (m : ℕ) (hm : 0 < m)
    (a : CW2376MarginalSupportedAddress m) (i : Fin 3) :
    ∃ j : Fin (cw2376ProfileLength m), a.1 i j = (1 : Fin 5) := by
  sorry
