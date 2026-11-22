-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ModuleRealization.conjugate_zpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:11:43.970055+00:00
-- url     : https://prove2.me/submissions/aae4d7d6-e8b5-4e60-ae6f-0af872894add

import Definitions.Def_Kourovka_Modules_SignedTameness
import Definitions.Def_Kourovka_Modules_ModuleRealization

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ModuleRealization
open FiniteCover ValuationModule SignedTameness TamenessCompactness
variable {k : ℕ} {M G : Type*} [AddCommGroup M] [Group G]
  [Module (GroupRing (Lattice k)) M]
namespace Kourovka.MetabelianEnumeration.ModuleRealization
theorem _root_.solution (x w : G) (c : ℤ) : conjugate (x ^ c) w = (conjugate x w) ^ c := by
  simpa [conjugate, MulAut.conj_apply] using (map_zpow ((MulAut.conj w⁻¹).toMonoidHom) x c)
end Kourovka.MetabelianEnumeration.ModuleRealization
