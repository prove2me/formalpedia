-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ModuleRealization.finite_realizing_polynomials
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:14:54.28329+00:00
-- url     : https://prove2.me/submissions/f5d09d5f-4c54-4fc3-bc62-f07d624856a9

import Definitions.Def_Kourovka_Modules_SignedTameness
import Definitions.Def_Kourovka_Modules_ModuleRealization
import Theorems.Thm_Kourovka_MetabelianEnumeration_ModuleRealization_polynomialSupport_encode
import Theorems.Thm_Kourovka_MetabelianEnumeration_ModuleRealization_polynomialWord_encode
import Theorems.Thm_Kourovka_MetabelianEnumeration_SignedTameness_finite_signed_centralizers


set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ModuleRealization
open FiniteCover ValuationModule SignedTameness TamenessCompactness
variable {k : ℕ} {M G : Type*} [AddCommGroup M] [Group G]
  [Module (GroupRing (Lattice k)) M]
namespace Kourovka.MetabelianEnumeration.ModuleRealization
theorem _root_.solution [Module.Finite (GroupRing (Lattice k)) M]
    (j : Multiplicative M →* G) (t : Fin k → G) (h : ActionCompatible j t)
    (ht : Tame (k := k) M) :
    ∃ ps : List (Polynomial k),
      (∀ p ∈ ps, ∀ m : M, j (Multiplicative.ofAdd m) =
        polynomialWord t (j (Multiplicative.ofAdd m)) p) ∧
      ConeVerifier.ConeCover (ps.map polynomialSupport) := by
  obtain ⟨ps, hact, hcover⟩ := finite_signed_centralizers ht
  refine ⟨ps.map encodeSigned, ?_, ?_⟩
  · intro p hp m
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [polynomialWord_encode j t h, hact q hq m]
  · simpa only [List.map_map, Function.comp_def, polynomialSupport_encode] using hcover
end Kourovka.MetabelianEnumeration.ModuleRealization
