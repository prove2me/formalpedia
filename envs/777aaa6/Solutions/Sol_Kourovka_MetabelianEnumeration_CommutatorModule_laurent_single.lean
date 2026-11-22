-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CommutatorModule.laurent_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:10:35.368868+00:00
-- url     : https://prove2.me/submissions/c33b8306-95f5-4944-bac5-dd015ed0ba03

import Definitions.Def_Kourovka_Modules_CommutatorModule
import Definitions.Def_Kourovka_Modules_LaurentAction

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CommutatorModule
variable {E Q L : Type} [Group E] [CommGroup Q] [AddCommGroup L]
variable (π : E →* Q) (hπ : Function.Surjective π) [IsMulCommutative π.ker]
variable (q : Multiplicative L →* Q)
namespace Kourovka.MetabelianEnumeration.CommutatorModule
theorem _root_.solution (u : L) (a : Additive π.ker) :
    letI := laurentModule π hπ q
    (((AddMonoidAlgebra.single u 1 : AddMonoidAlgebra ℤ L) • a) : Additive π.ker).toMul =
      rightConjugation π hπ (q (Multiplicative.ofAdd u)) a.toMul := by
  letI := laurentModule π hπ q
  change ((Representation.asAlgebraHom ((rightRepresentation π hπ).comp q))
    ((AddMonoidAlgebra.toMultiplicative ℤ L) (AddMonoidAlgebra.single u 1)) a).toMul = _
  have hsingle : (AddMonoidAlgebra.toMultiplicative ℤ L) (AddMonoidAlgebra.single u 1) =
      MonoidAlgebra.single (Multiplicative.ofAdd u) 1 :=
    by simp [AddMonoidAlgebra.toMultiplicative]
  rw [hsingle, Representation.asAlgebraHom_single_one]
  rfl
end Kourovka.MetabelianEnumeration.CommutatorModule
