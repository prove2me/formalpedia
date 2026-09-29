-- Prove2me | solution 1 for lean_workbook_plus_76520
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:14:16.817148+00:00
-- url     : https://prove2.me/submissions/42c6cadf-f3d4-44cd-b9b9-1d496782e1e0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (G : Type*) [CommGroup G] [Finite G] : 
  ∃ g : G, ∀ h : G, orderOf g ∣ orderOf h := by
  intros
  refine ⟨1, ?_⟩ <;> norm_num at *
