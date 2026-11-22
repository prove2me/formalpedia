-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SignedTameness.finite_signed_centralizers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:13:30.266329+00:00
-- url     : https://prove2.me/submissions/12de2f31-ffc9-42f1-81af-551afcb9b370

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Modules_SignedTameness
import Theorems.Thm_Kourovka_MetabelianEnumeration_SignedTameness_character_ne_zero
import Theorems.Thm_Kourovka_MetabelianEnumeration_SignedTameness_positive_signed_support
import Theorems.Thm_Kourovka_MetabelianEnumeration_SignedTameness_negative_signed_support
import Theorems.Thm_Kourovka_MetabelianEnumeration_TamenessCompactness_finite_support_selection
import Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_positive_centralizer_of_finite


set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SignedTameness
open FiniteCover ConeVerifier ValuationModule TamenessCompactness
variable {k : ℕ} {M : Type*} [AddCommGroup M] [Module (GroupRing (Lattice k)) M]
namespace Kourovka.MetabelianEnumeration.SignedTameness
theorem _root_.solution [Module.Finite (GroupRing (Lattice k)) M]
    (ht : Tame (k := k) M) :
    ∃ ps : List (SignedPolynomial k),
      (∀ p ∈ ps, ∀ m : M, p.2 • m = m) ∧ ConeCover (ps.map signedSupport) := by
  apply finite_support_selection signedSupport (fun p => ∀ m : M, p.2 • m = m)
  intro x hx
  rcases ht x hx with hp | hn
  · letI := hp
    obtain ⟨p, hpos, hact⟩ := positive_centralizer_of_finite (M := M)
      (character x) (character_ne_zero hx)
    exact ⟨(true, p), hact, positive_signed_support p hpos⟩
  · letI := hn
    obtain ⟨p, hpos, hact⟩ := positive_centralizer_of_finite (M := M)
      (-character x) (neg_ne_zero.mpr (character_ne_zero hx))
    exact ⟨(false, p), hact, negative_signed_support p hpos⟩
end Kourovka.MetabelianEnumeration.SignedTameness
