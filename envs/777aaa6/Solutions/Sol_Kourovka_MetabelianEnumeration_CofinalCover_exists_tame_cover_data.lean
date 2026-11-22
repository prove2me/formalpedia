-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.exists_tame_cover_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:19:00.955099+00:00
-- url     : https://prove2.me/submissions/1c67805c-433a-4b10-844d-4b4f8aab45ac

import Definitions.Def_Kourovka_Cofinality_LatticePullback
import Definitions.Def_Kourovka_Modules_ModuleRealization
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Modules_FiniteModuleGenerators
import Definitions.Def_Kourovka_Cofinality_CofinalRealization
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_laurent_action_compatible
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_exists_cover_data_of_tame

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
theorem _root_.solution (hπ : Function.Surjective π) :
    letI := laurentModule π hπ (MonoidHom.id (Multiplicative (Lattice k)))
    Module.Finite (GroupRing (Lattice k)) (Additive π.ker) →
    Tame (k := k) (Additive π.ker) →
    ∃ a : ℕ, 1 ≤ a ∧ ∃ data : Datum k a,
      ConeVerifier.ConeCover (data.polynomials.map polynomialSupport) ∧
      ∀ radius : ℕ, ∃ f : FiniteCover.GroupOf data radius →* E, Function.Surjective f := by
  classical
  letI := laurentModule π hπ (MonoidHom.id (Multiplicative (Lattice k)))
  intro hfinite htame
  letI := hfinite
  choose t ht using (fun i : Fin k => hπ (Multiplicative.ofAdd (Pi.single i 1)))
  exact exists_cover_data_of_tame π t ht (laurent_action_compatible π hπ t ht) htame
end Kourovka.MetabelianEnumeration.CofinalCover
