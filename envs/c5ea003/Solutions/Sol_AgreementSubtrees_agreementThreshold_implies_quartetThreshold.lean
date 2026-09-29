-- Prove2me | solution 1 for AgreementSubtrees.agreementThreshold_implies_quartetThreshold
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T15:04:02.993245+00:00
-- url     : https://prove2.me/submissions/cbd355c2-d712-4c5c-a8e8-81bcd3d17429

import Mathlib
import Definitions.Def_Novelty_Core

open Finset AgreementSubtrees in
theorem solution {N k n : ℕ} (hn : 4 ≤ n)
    (h : IsAgreementThreshold N k n) : IsAgreementThreshold N k 4 := by
  intro T
  obtain ⟨A, hA, R, hR⟩ := h T
  -- shrink the common agreement set to any 4 of its leaves
  obtain ⟨B, hBA, hB⟩ := Finset.exists_subset_card_eq (show 4 ≤ A.card by omega)
  refine ⟨B, hB, AgreementSubtrees.restrict R B, fun i hi => ?_⟩
  rw [← hR i hi]
  unfold AgreementSubtrees.restrict
  rw [Finset.image_image]
  congr 1
  funext s
  simp only [Function.comp, Finset.inter_assoc, Finset.inter_eq_right.2 hBA]
