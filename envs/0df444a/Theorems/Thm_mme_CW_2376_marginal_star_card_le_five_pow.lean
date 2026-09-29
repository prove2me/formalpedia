-- Prove2me | Theorems.Thm_mme_CW_2376_marginal_star_card_le_five_pow
-- name    : mme_CW_2376_marginal_star_card_le_five_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:36:05.751656+00:00
-- url     : https://prove2.me/theorems/25e0eb73-f3d6-46f3-acbf-1ac2a45d19e8
-- title:
--   A full marginal-supported CW completion star has at most five to the profile length elements
-- statement:
--   Fix one of the three mode words of an address in the full Coppersmith--Winograd marginal-supported hypergraph at profile length $N$. The number of supported completions with that fixed mode word is at most
--
--   $$
--   5^N.
--   $$
--
--   Indeed, on the grade-sum-four support, any two mode words determine the third. Projection of a completion to either remaining mode is therefore injective, and that mode has only $5^N$ possible words. This deliberately crude bound is used only to choose the prime modulus in the Salem--Spencer hashing step.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), the supported completion graph and Salem--Spencer pruning on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_hash_incidence_universes
import Theorems.Thm_mme_CW_2376_supported_two_modes_determine_address

open MME

set_option autoImplicit false

theorem mme_CW_2376_marginal_star_card_le_five_pow
    (m : ℕ) (i : Fin 3) (a : CW2376MarginalSupportedAddress m) :
    ((cw2376MarginalSupportedUniverse m).filter
      (fun b => b.1 i = a.1 i)).card ≤
        5 ^ cw2376ProfileLength m := by
  sorry
