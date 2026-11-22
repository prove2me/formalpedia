-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.laurent_action_compatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:14:56.260152+00:00
-- url     : https://prove2.me/submissions/5dbce173-02a3-4280-863a-397b938585f3

import Definitions.Def_Kourovka_Cofinality_LatticePullback
import Definitions.Def_Kourovka_Modules_ModuleRealization
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Modules_FiniteModuleGenerators
import Definitions.Def_Kourovka_Cofinality_CofinalRealization
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_projection_orderedWord
import Theorems.Thm_Kourovka_MetabelianEnumeration_CommutatorModule_laurent_single_image


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
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution (hπ : Function.Surjective π) (t : Fin k → E)
    (ht : ∀ i, π (t i) = Multiplicative.ofAdd (Pi.single i 1)) :
    letI := laurentModule π hπ (MonoidHom.id (Multiplicative (Lattice k)))
    ActionCompatible (kernelInclusion π) t := by
  letI := laurentModule π hπ (MonoidHom.id (Multiplicative (Lattice k)))
  intro u m
  exact laurent_single_image π hπ (MonoidHom.id _) u (orderedWord t u)
    (projection_orderedWord π t ht u).symm m
end Kourovka.MetabelianEnumeration.CofinalCover
