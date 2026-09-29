-- Prove2me | Theorems.Thm_mme_dwz_source_aligned_address_word_survives_iff_exists_nonhole
-- name    : mme_dwz_source_aligned_address_word_survives_iff_exists_nonhole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T13:49:17.974472+00:00
-- url     : https://prove2.me/theorems/0a39bb99-980a-4083-8382-09f71dd29aa6
-- title:
--   The source-aligned Z-basis mask is exactly the literal useful-block nonhole mask
-- statement:
--   Fix one retained Table-2 outer word and a literal broken-copy nonhole set. A canonical $Z$-basis word of its source-aligned coarse address survives the broken projection if and only if its pointwise fine pair word is exactly the value of some literal useful block in the nonhole set:
--
--   $$
--   W\text{ survives}\quad\Longleftrightarrow\quad\exists z\in\mathrm{nonholes},\; z=\mathrm{fineZ}(W).
--   $$
--
--   This identifies the basis-level source projection with the Claim-6.8 `UsefulBlock` mask. The equivalence is literal and proof-independent; it does not replace membership by a cardinality statement.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.4--5.5, Definition 6.3, and Claim 6.8; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_source_aligned_broken_obj

open MME Module

universe u

open MME.DWZSourceAligned

set_option autoImplicit false

theorem mme_dwz_source_aligned_address_word_survives_iff_exists_nonhole
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (W : AddressZWord outer) :
    addressWordSurvives m outer copy W ↔
      ∃ small : DWZTable2StandardForm.UsefulBlock m outer,
        small ∈ copy.nonholes ∧ small.1 = addressFineZ W := by
  sorry
