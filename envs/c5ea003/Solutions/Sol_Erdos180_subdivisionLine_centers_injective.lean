-- Prove2me | solution 1 for Erdos180.subdivisionLine_centers_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:47:33.22542+00:00
-- url     : https://prove2.me/submissions/c6e16e7f-83c4-4250-8b2f-13298b24dbde

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Field.Defs
import Mathlib.Combinatorics.SimpleGraph.Copy

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    (C : Fin k → SymplecticLine K)
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inr (C center)) :
    Function.Injective C := by
  intro i j hij
  apply Sum.inr.inj
  apply Sum.inl.inj
  apply copy.injective
  change copy (.inl (.inr i)) = copy (.inl (.inr j))
  rw [hcenter i, hcenter j, hij]
