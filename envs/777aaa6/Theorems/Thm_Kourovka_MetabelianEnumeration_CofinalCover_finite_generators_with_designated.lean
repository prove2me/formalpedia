-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_finite_generators_with_designated
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.finite_generators_with_designated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:58:25.356742+00:00
-- url     : https://prove2.me/theorems/dd4c07b0-9357-4f3b-8ace-3b8430c11fe2
-- title:
--   Cofinal Cover: finite generators with designated
-- statement:
--   Enlarge any finite spanning family by specified elements and zero, then
--   index it by a nonempty finite ordinal.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/FiniteModuleGenerators.lean#L24-L53
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/FiniteModuleGenerators.lean#L24-L53

import Definitions.Def_Kourovka_Modules_ModuleRealization
import Definitions.Def_Kourovka_Modules_FiniteModuleGenerators
set_option autoImplicit true
noncomputable section
set_option maxHeartbeats 50000
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
open FiniteCover ValuationModule

theorem Kourovka.MetabelianEnumeration.CofinalCover.finite_generators_with_designated {k : ℕ} {M : Type} [AddCommGroup M]
    [Module (GroupRing (Lattice k)) M] [Module.Finite (GroupRing (Lattice k)) M]
    (c : Fin k × Fin k → M) :
    ∃ a : ℕ, 1 ≤ a ∧ ∃ (A : Fin a → M) (designated : Fin k → Fin k → Fin a),
      Submodule.span (GroupRing (Lattice k)) (Set.range A) = ⊤ ∧
      ∀ i j, A (designated i j) = c (i, j) := by sorry
