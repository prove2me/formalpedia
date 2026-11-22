-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ModuleRealization.compatible_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:11:42.309559+00:00
-- url     : https://prove2.me/submissions/58bb9203-bf22-4ddd-8699-9bd5de7b0b85

import Definitions.Def_Kourovka_Modules_SignedTameness
import Definitions.Def_Kourovka_Modules_ModuleRealization

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ModuleRealization
open FiniteCover ValuationModule SignedTameness TamenessCompactness
variable {k : ℕ} {M G : Type*} [AddCommGroup M] [Group G]
  [Module (GroupRing (Lattice k)) M]
namespace Kourovka.MetabelianEnumeration.ModuleRealization
theorem _root_.solution (j : Multiplicative M →* G) (t : Fin k → G)
    (h : ActionCompatible j t) (u : Lattice k) (m : M) :
    conjugate (j (Multiplicative.ofAdd m)) ((orderedWord t (-u))⁻¹) =
      j (Multiplicative.ofAdd ((AddMonoidAlgebra.single u 1 : GroupRing (Lattice k)) • m)) := by
  have hh := h (-u) ((AddMonoidAlgebra.single u 1 : GroupRing (Lattice k)) • m)
  have hs : (AddMonoidAlgebra.single (-u) 1 : GroupRing (Lattice k)) •
      ((AddMonoidAlgebra.single u 1 : GroupRing (Lattice k)) • m) = m := by
    rw [← mul_smul, AddMonoidAlgebra.single_mul_single]
    simp [← AddMonoidAlgebra.one_def]
  rw [hs] at hh
  rw [hh]
  simp [conjugate, mul_assoc]
end Kourovka.MetabelianEnumeration.ModuleRealization
