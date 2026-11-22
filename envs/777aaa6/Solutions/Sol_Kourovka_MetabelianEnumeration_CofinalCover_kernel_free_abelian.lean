-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.kernel_free_abelian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:09:55.668174+00:00
-- url     : https://prove2.me/submissions/f3a0a066-f8e2-45f8-a901-26cdefe0a66c

import Definitions.Def_Kourovka_Cofinality_CofinalCover
import Definitions.Def_Kourovka_Presentations_FreeAbelianPresentation
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Finiteness.Finsupp
import Definitions.Def_Kourovka_Presentations_PullbackPresentation

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
variable {α : Type} [Fintype α]
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution {Q : Type} [CommGroup Q]
    (q : Multiplicative (FreeAbelianGroup α) →* Q) :
    ∃ (β : Type) (finiteβ : Fintype β), letI := finiteβ
      Nonempty (Multiplicative (FreeAbelianGroup β) ≃* q.ker) := by
  let K : Submodule ℤ (FreeAbelianGroup α) := LinearMap.ker (q.toAdditiveRight.toIntLinearMap)
  let β := Module.Free.ChooseBasisIndex ℤ K
  let b := Module.Free.chooseBasis ℤ K
  let eadd : K ≃+ FreeAbelianGroup β :=
    b.repr.toAddEquiv.trans (FreeAbelianGroup.equivFinsupp β).symm
  let etag : Multiplicative K ≃* q.ker := {
    toFun := fun x => ⟨Multiplicative.ofAdd x.toAdd.val, x.toAdd.property⟩
    invFun := fun x => Multiplicative.ofAdd ⟨x.val.toAdd, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  exact ⟨β, inferInstance, ⟨eadd.symm.toMultiplicative.trans etag⟩⟩
end Kourovka.MetabelianEnumeration.CofinalCover
