-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ModuleRealization.polynomialWord_encode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:13:30.743743+00:00
-- url     : https://prove2.me/submissions/416cb344-00d5-40b3-9472-cfc564486c00

import Definitions.Def_Kourovka_Modules_SignedTameness
import Definitions.Def_Kourovka_Modules_ModuleRealization
import Theorems.Thm_Kourovka_MetabelianEnumeration_ModuleRealization_map_sum
import Theorems.Thm_Kourovka_MetabelianEnumeration_ModuleRealization_smul_as_sum
import Theorems.Thm_Kourovka_MetabelianEnumeration_ModuleRealization_compatible_inverse
import Theorems.Thm_Kourovka_MetabelianEnumeration_ModuleRealization_conjugate_zpow

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ModuleRealization
open FiniteCover ValuationModule SignedTameness TamenessCompactness
variable {k : ℕ} {M G : Type*} [AddCommGroup M] [Group G]
  [Module (GroupRing (Lattice k)) M]
namespace Kourovka.MetabelianEnumeration.ModuleRealization
theorem _root_.solution (j : Multiplicative M →* G) (t : Fin k → G)
    (h : ActionCompatible j t) (p : SignedPolynomial k) (m : M) :
    polynomialWord t (j (Multiplicative.ofAdd m)) (encodeSigned p) =
      j (Multiplicative.ofAdd (p.2 • m)) := by
  rw [smul_as_sum, map_sum]
  simp only [polynomialWord, encodeSigned, List.map_map]
  congr 1
  apply List.map_congr_left
  intro u _
  simp only [Function.comp_apply, conjugate_zpow, ofAdd_zsmul, map_zpow]
  cases hb : p.1
  · simpa only [hb, Bool.false_eq_true, if_false] using
      congrArg (fun x : G => x ^ p.2 u) (compatible_inverse j t h u m)
  · simpa only [hb, if_true] using
      congrArg (fun x : G => x ^ p.2 u) (h u m).symm
end Kourovka.MetabelianEnumeration.ModuleRealization
