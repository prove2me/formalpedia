-- Prove2me | Theorems.Thm_mme_dwz_central_022_202_power_word_coordinates
-- name    : mme_dwz_central_022_202_power_word_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T05:36:55.167989+00:00
-- url     : https://prove2.me/theorems/9d57ca2f-6325-4ab3-b9e4-6746def1607f
-- title:
--   Exact collapsed coordinates of central 022 and 202 channel words
-- statement:
--   Let \(w=(c_0,\ldots,c_{m-1})\) be a word in the fine central channel set of the squared Coppersmith–Winograd tensor. Under the explicit little-endian flattening of the corresponding matrix-multiplication tensor power, the nested basis word is sent mode by mode to the standard basis vector whose variable coordinate is\n\n$$\n\sum_{i=0}^{m-1} c_i(q^2+2)^i.\n$$\n\nThis holds simultaneously for the 022 constituent and its 202 mode rotation. In particular, the theorem identifies the image of each named source-channel word, rather than merely identifying the dimension of the ambient tensor power.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3 and Appendix A, https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_central_power_word_coordinates

open MME
open MME.DWZFineChannel

universe u

set_option autoImplicit false

theorem mme_dwz_central_022_202_power_word_coordinates
    (K : Type u) [Field K] (q m : ℕ) :
    (∀ (w : Fin m → Fine022Channel q) (s : Fin 3),
      littleEndianPowerMaps K 1 1 (q ^ 2 + 2) m s
          (central022MMWordVec K q m w s) =
        central022FlatMMVec K q m (fineChannelWordIndex q m w) s) ∧
    (∀ (w : Fin m → Fine202Channel q) (s : Fin 3),
      littleEndianPowerMaps K (q ^ 2 + 2) 1 1 m s
          (central202MMWordVec K q m w s) =
        central202FlatMMVec K q m (fineChannelWordIndex q m w) s) := by
  sorry
