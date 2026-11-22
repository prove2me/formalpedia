-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ModuleRealization.polynomialSupport_encode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:11:26.471672+00:00
-- url     : https://prove2.me/submissions/4f2243ef-96b3-4bd1-9755-6f609f2b77f8

import Definitions.Def_Kourovka_Modules_SignedTameness
import Definitions.Def_Kourovka_Modules_ModuleRealization

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ModuleRealization
open FiniteCover ValuationModule SignedTameness TamenessCompactness
variable {k : ℕ} {M G : Type*} [AddCommGroup M] [Group G]
  [Module (GroupRing (Lattice k)) M]
namespace Kourovka.MetabelianEnumeration.ModuleRealization
theorem _root_.solution (p : SignedPolynomial k) :
    polynomialSupport (encodeSigned p) = signedSupport p := by
  simp only [polynomialSupport, encodeSigned, signedSupport, List.map_map]
  apply List.map_congr_left
  intro u _
  funext i
  cases p.1 <;> simp
end Kourovka.MetabelianEnumeration.ModuleRealization
