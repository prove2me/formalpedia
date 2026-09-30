-- Prove2me | solution 1 for lean_workbook_plus_42412
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:27:28.690325+00:00
-- url     : https://prove2.me/submissions/29cf7ffd-9d3a-42de-88d4-7adec44a8b05

import Mathlib.GroupTheory.Index

set_option autoImplicit false

theorem solution (G : Type*) [Group G] [Infinite G]
    (H : Subgroup G) [H.FiniteIndex] :
    ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧ N ≤ H := by
  exact ⟨H.normalCore, inferInstance, inferInstance, H.normalCore_le⟩

#print axioms solution
