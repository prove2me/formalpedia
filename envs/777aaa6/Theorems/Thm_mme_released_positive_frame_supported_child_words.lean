-- Prove2me | Theorems.Thm_mme_released_positive_frame_supported_child_words
-- name    : mme_released_positive_frame_supported_child_words
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-24T03:00:47.851828+00:00
-- url     : https://prove2.me/theorems/468b9470-63e3-4063-9982-d6affa3078b3
-- title:
--   Exact supported child words for every compact released frame
-- statement:
--   For every released inner region r and every natural-number scale k, any compact positive integer frame admits three physical fine words x_0, x_1, x_2 with the exact central child histograms. Write x_i(q) for the numeric entry in mode i at physical coordinate q, and C_i(c,w) for the number of split positions in cell c carrying child word w. Then
--
--   $$\sum_{i=0}^{2} x_i(q)=2, \qquad C_i(c,w)=k\,\mu_{r,i}(c,w).$$
--
--   Here the split uses the frame's own position enumeration, and mu is the released compact central profile. Every split child word also has the grade prescribed by its cell.
--
--   The result keeps the reference address and enumeration already chosen by the frame. It assumes neither a tolerance nor a repair budget, and it handles cells of zero mass. It is conditional on the supplied frame; it does not assert that a frame exists at scale zero. Positive-scale frame existence is a separate accepted theorem.
--
--   Exact histograms imply membership in every central child window of nonnegative radius for a step constructed from the same frame. This supplies the supported-window witness used to prove that a graded tolerance stage has at least one type. The theorem does not assert a matrix-volume bound or complete the recursive joint construction.
-- source:
--   New finite-data realization lemma for the released compact profiles. It uses Robertboy18's joint-histogram realization theorem p2m:theorem/0703f3f2-a79a-4e3a-93bb-a0f7d154209c (accepted proof p2m:solution/d4f8e3aa-913a-41cd-828d-e065df03ae7b), the compact tables p2m:theorem/60610bd3-0675-4be4-a731-ca71c173a5bc contributed by marwahaha, and the common integer profiles p2m:theorem/3d489536-019f-46c1-b6c3-52ee24f948d0 contributed by Robertboy18 from raresbuhai's released exact seed p2m:theorem/cb80ec03-0b0a-4b6c-a75e-ca788b94d914. The local cell-fiber cardinality argument is copied verbatim from raresbuhai's accepted proof p2m:solution/50983a64-7873-4293-b499-5e40f94a5eef of p2m:theorem/42ce2054-4a77-4ab8-872d-5d87385fc333. The six accepted positive-profile correspondences transport the joint counts to the 88 compact labels. The existing positive-frame existence result is p2m:theorem/8aa8d8f3-b4a4-4716-9fdf-b63581bd2434.

import Definitions.Def_mme_released_positive_integer_frame_data

open BigOperators MME MME.RecursiveYZ MME.CompleteSplit MME.RegionRealization
  MME.ProfiledCW MME.RecursiveYZ.CWCells MME.ReleasedPositiveInteger
set_option autoImplicit false

theorem mme_released_positive_frame_supported_child_words (region : Fin 6) (k : ℕ) (frame : Frame region k) :
    ∃ x : Fin 3 → FineWord (ReleasedJointInterior.blocks region k * 4),
      supported x ∧ ∀ i,
        Graded (RecStage.htotal3 region) i frame.reference
          (split (ell := 2) frame.positions (ReleasedJointInterior.positions_length region k) (x i)) ∧
        Useful (fullCell (RecStage.htotal3 region) frame.reference)
          (fun c w => k * RecStage.mu3 region i c w)
          (split (ell := 2) frame.positions (ReleasedJointInterior.positions_length region k) (x i)) := by sorry
