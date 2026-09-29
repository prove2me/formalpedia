-- Prove2me | solution 1 for BoltzmannBridge.Filtration.sublevel_mono
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T00:07:58.794681+00:00
-- url     : https://prove2.me/submissions/77a27697-510c-43fa-8bcc-e60e7d5bdc37

import Mathlib
import Definitions.Def_Applications_BoltzmannBridge_HigherPersistence
open BoltzmannBridge BoltzmannBridge.Filtration in
theorem solution {α : Type*} (F : Filtration α) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    F.sublevelFaces t₁ ⊆ F.sublevelFaces t₂ := by
  -- a face of weight `≤ t₁` has weight `≤ t₂`
  intro σ hσ
  exact le_trans hσ h
