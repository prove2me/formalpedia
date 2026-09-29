-- Prove2me | solution 1 for Doppelganger.injective_drive_of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:34:03.959808+00:00
-- url     : https://prove2.me/submissions/0882f31f-47bc-44db-8c78-b6449df946db

import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Boundary
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core

open Doppelganger

variable {S I : Type*}

theorem solution {δ : S → I → S} {w : List I}
    (h : ∀ i ∈ w, Function.Injective (δ · i)) : Function.Injective (drive δ w) := by
  induction w with
  | nil =>
      intro s t hst
      simpa [drive] using hst
  | cons i w ih =>
      intro s t hst
      have hi : Function.Injective (δ · i) := h i (by simp)
      have hw : ∀ j ∈ w, Function.Injective (δ · j) := fun j hj => h j (by simp [hj])
      have hst' : drive δ w (δ s i) = drive δ w (δ t i) := by
        simpa [drive] using hst
      exact hi (ih hw hst')
