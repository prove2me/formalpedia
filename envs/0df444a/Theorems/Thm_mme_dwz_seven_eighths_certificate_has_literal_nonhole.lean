-- Prove2me | Theorems.Thm_mme_dwz_seven_eighths_certificate_has_literal_nonhole
-- name    : mme_dwz_seven_eighths_certificate_has_literal_nonhole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T11:02:25.004258+00:00
-- url     : https://prove2.me/theorems/4e836631-5fc1-4b20-9ed5-9cb3bfa64ce7
-- title:
--   A seven-eighths broken-copy certificate contains a literal nonhole
-- statement:
--   Let $B$ be a nonempty finite set of available small blocks, and let $C ⊆ B$ be the blocks that remain nonholes in a broken copy. If the exact Claim-6.8 certificate
--
--   $$7|B| \le 8|C|$$
--
--   holds, then $C$ contains an actual block. This converts the quantitative seven-eighths conclusion into the literal membership witness needed by the Step-2 nonhole direct-sum restriction.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Claim 6.8 and Definition 5.5; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_hole_cover_data

set_option autoImplicit false

theorem mme_dwz_seven_eighths_certificate_has_literal_nonhole
    {Block : Type*} [Fintype Block] [Nonempty Block]
    (copy : MME.DWZSquare.BrokenBlockCopy Block)
    (hseven :
      7 * Fintype.card Block ≤ 8 * copy.nonholes.card) :
    ∃ z : Block, z ∈ copy.nonholes := by
  sorry
