-- Prove2me | solution 1 for TropicalLA.diagBotExample_not_stronglyConnected
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T08:00:05.468136+00:00
-- url     : https://prove2.me/submissions/0eebe7c7-c2b6-4fa6-a3aa-00ecb361da7b

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
open TropicalLA in
theorem solution : ¬ StronglyConnected diagBotExample := by
  intro h
  -- the support of a diagonal matrix relates an index only to itself
  have hsupp : ∀ i j : Fin 2, Supp diagBotExample i j → i = j := by
    intro i j hij
    by_contra hne
    exact hij (by simp [diagBotExample, hne])
  -- so the transitive closure cannot leave the diagonal either
  have hkey : ∀ i j : Fin 2, Relation.TransGen (Supp diagBotExample) i j → i = j := by
    intro i j hr
    induction hr with
    | single hs => exact hsupp _ _ hs
    | tail hik hkj ih => exact ih.trans (hsupp _ _ hkj)
  have h01 := hkey 0 1 (h 0 1)
  simp at h01
