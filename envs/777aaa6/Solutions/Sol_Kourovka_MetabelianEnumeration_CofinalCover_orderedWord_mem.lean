-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.orderedWord_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:13:50.213732+00:00
-- url     : https://prove2.me/submissions/5a18a5c4-f417-4b59-adfa-abff609fb3e7

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
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution (t : Fin k → E) (K : Subgroup E) (ht : ∀ i, t i ∈ K)
    (v : Lattice k) : orderedWord t v ∈ K := by
  apply K.list_prod_mem
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact K.zpow_mem (ht i) _
end Kourovka.MetabelianEnumeration.CofinalCover
