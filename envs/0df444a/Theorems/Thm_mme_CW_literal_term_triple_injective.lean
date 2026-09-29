-- Prove2me | Theorems.Thm_mme_CW_literal_term_triple_injective
-- name    : mme_CW_literal_term_triple_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:01:52.963196+00:00
-- url     : https://prove2.me/theorems/dd886154-2a24-4e7f-9f7a-7a718d6678fa
-- title:
--   Literal CW summands have unique three-coordinate addresses
-- statement:
--   For every CW parameter $q$, a literal summand of the Coppersmith--Winograd tensor is uniquely determined by its three basis coordinates. Ordinary summands are distinguished by the position of the zero coordinate and their shared middle index, while the three exceptional summands are distinguished by the position of the top coordinate. This injectivity permits a coordinate functional to isolate one selected term in a tensor-power expansion.
-- source:
--   D. Coppersmith and S. Winograd, Matrix multiplication via arithmetic progressions, J. Symbolic Computation 9 (1990), definition of the CW tensor support.

import Definitions.Def_mme_CW_fourth_literal_support_words

set_option autoImplicit false

theorem mme_CW_literal_term_triple_injective (q : ℕ) :
    Function.Injective (MME.StothersFourth.cwLiteralTermTriple q) := by
  sorry
