-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ModuleRealization.single_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:11:34.586092+00:00
-- url     : https://prove2.me/submissions/c5fbadc1-0d3b-47c1-93b6-1f42dbb0c7fb

import Definitions.Def_Kourovka_Modules_SignedTameness
import Definitions.Def_Kourovka_Modules_ModuleRealization

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ModuleRealization
open FiniteCover ValuationModule SignedTameness TamenessCompactness
variable {k : ℕ} {M G : Type*} [AddCommGroup M] [Group G]
  [Module (GroupRing (Lattice k)) M]
namespace Kourovka.MetabelianEnumeration.ModuleRealization
theorem _root_.solution (u : Lattice k) (c : ℤ) (m : M) :
    (AddMonoidAlgebra.single u c : GroupRing (Lattice k)) • m =
      c • ((AddMonoidAlgebra.single u 1 : GroupRing (Lattice k)) • m) := by
  have h : (AddMonoidAlgebra.single u c : GroupRing (Lattice k)) =
      c • (AddMonoidAlgebra.single u 1 : GroupRing (Lattice k)) := by
    change (Finsupp.single u c : Lattice k →₀ ℤ) = c • Finsupp.single u (1 : ℤ)
    simp
  rw [h, smul_assoc]
end Kourovka.MetabelianEnumeration.ModuleRealization
