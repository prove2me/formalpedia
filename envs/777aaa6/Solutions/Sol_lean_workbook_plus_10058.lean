-- Prove2me | solution 1 for lean_workbook_plus_10058
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:37.507435+00:00
-- url     : https://prove2.me/submissions/c3aedc64-0180-4eb8-8f86-2a651a7cabfb

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (E : Type) (A B C D : Set E) (h1 : A ⊆ B) (h2 : C ⊆ D) :
  A ∩ C ⊆ B ∩ D := by
  intro x hx
  exact ⟨h1 hx.1,h2 hx.2⟩
