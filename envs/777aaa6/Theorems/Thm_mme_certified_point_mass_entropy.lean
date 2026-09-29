-- Prove2me | Theorems.Thm_mme_certified_point_mass_entropy
-- name    : mme_certified_point_mass_entropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T05:36:17.283008+00:00
-- url     : https://prove2.me/theorems/f7c8a547-b7a5-401c-9b6b-26591e95b735
-- title:
--   A distribution concentrated on one letter has zero entropy
-- statement:
--   A distribution concentrated on a single letter has zero entropy, and so does the frequency of a
--   profile supported on a single word.
--
--   This is worth stating separately because a great many parts of a compatibility partition are exactly
--   of this kind. For those, no certificate is needed at all: their contribution to the potential is
--   zero, not merely small.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_certified_entropy_bridge

open BigOperators MME MME.RegionRate MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u v

theorem mme_certified_point_mass_entropy :
    (∀ {W : Type u} [Fintype W] (p : W → ℚ) (w0 : W),
      (∀ w, p w = if w = w0 then 1 else 0) →
      entropy (fun w ↦ ((p w : ℚ) : ℝ)) = 0) ∧
    ∀ {C : Type v} {W : Type u} [Fintype W] (mu : C → W → ℕ) (c : C) (w0 : W),
      (∀ w, w ≠ w0 → mu c w = 0) → mu c w0 ≠ 0 →
      entropy (fun w ↦ ((freqQ mu c w : ℚ) : ℝ)) = 0 := by sorry
