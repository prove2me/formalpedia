-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_closure_module_generators
-- name    : Kourovka.MetabelianEnumeration.CofinalCover.closure_module_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:13:46.577355+00:00
-- url     : https://prove2.me/theorems/e3a6e27d-cdfa-4d72-97af-ac35c1b737b9
-- title:
--   Cofinal Cover: closure module generators
-- statement:
--   Finite module generators together with lifts of a lattice basis generate
--   the actual extension group.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalRealization.lean#L74-L115
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Cofinality/CofinalRealization.lean#L74-L115

import Definitions.Def_Kourovka_Cofinality_LatticePullback
import Definitions.Def_Kourovka_Modules_ModuleRealization
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Modules_FiniteModuleGenerators
import Definitions.Def_Kourovka_Cofinality_CofinalRealization
set_option autoImplicit true
noncomputable section
set_option maxHeartbeats 50000
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
open FiniteCover CommutatorModule ModuleRealization ValuationModule SignedTameness
open TamenessCompactness
variable {k : ℕ} {E : Type} [Group E]
variable (π : E →* Multiplicative (Lattice k))
variable [IsMulCommutative π.ker]
variable [Module (GroupRing (Lattice k)) (Additive π.ker)]

theorem Kourovka.MetabelianEnumeration.CofinalCover.closure_module_generators {a : ℕ} (t : Fin k → E)
    (ht : ∀ i, π (t i) = Multiplicative.ofAdd (Pi.single i 1))
    (hact : ActionCompatible (kernelInclusion π) t) (A : Fin a → Additive π.ker)
    (hA : Submodule.span (GroupRing (Lattice k)) (Set.range A) = ⊤) :
    Subgroup.closure (Set.range t ∪ Set.range (fun i => (A i).toMul.val)) = ⊤ := by sorry
