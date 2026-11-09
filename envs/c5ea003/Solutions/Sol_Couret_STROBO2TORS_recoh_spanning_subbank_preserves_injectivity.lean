-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_spanning_subbank_preserves_injectivity
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:18.868535+00:00
-- url     : https://prove2.me/submissions/b14d42fb-94db-4c54-b78e-dc5f1a0abe58

import Aesop
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohRankKernel_9b83850e485b
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

set_option autoImplicit false

/-!
RECOH: information-set extraction for a family of linear coordinate probes.

The general independent-subfamily theorem is standard linear algebra:
retain an independent subfamily spanning the original coordinate forms.
For a binary r-dimensional coordinate space, injectivity implies that
precisely r extracted coordinates suffice. These are not additional
conditions on the bank. Converting arbitrary additive binary characters
to linear forms is a separate interface.
-/

namespace Couret.STROBO2TORS

universe u

/-- A family of coordinate forms and any subfamily generating the same
span have the same ability to distinguish vectors. -/
theorem p2m_local_recoh_spanning_subbank_preserves_injectivity
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    {ι κ : Type*}
    (bank : ι → Module.Dual K V) (selected : κ → ι)
    (hspan : Submodule.span K (Set.range (bank ∘ selected)) =
      Submodule.span K (Set.range bank))
    (hinj : Function.Injective (fun x : V => fun i : ι => bank i x)) :
    Function.Injective (fun x : V => fun j : κ => bank (selected j) x) := by
  intro x y hxy
  apply hinj
  funext i
  have hsel : ∀ j : κ, bank (selected j) (x - y) = 0 := by
    intro j
    have hj := congrArg (fun f : κ → K => f j) hxy
    simpa only [map_sub, sub_eq_zero] using hj
  have hle : Submodule.span K (Set.range (bank ∘ selected)) ≤
      LinearMap.ker (LinearMap.applyₗ (x - y)) := by
    apply Submodule.span_le.mpr
    rintro f ⟨j, rfl⟩
    change bank (selected j) (x - y) = 0
    exact hsel j
  have hi : bank i (x - y) = 0 := by
    have hm : bank i ∈
        Submodule.span K (Set.range (bank ∘ selected)) := by
      rw [hspan]
      exact Submodule.subset_span (Set.mem_range_self i)
    exact hle hm
  simpa only [map_sub, sub_eq_zero] using hi





end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1 p2m_u_2 p2m_u_3
theorem solution : ∀ {K : Type p2m_u_0} [inst : Field.{p2m_u_0} K] {V : Type p2m_u_1} [inst_1 : AddCommGroup.{p2m_u_1} V]
  [inst_2 :
    @_root_.Module.{p2m_u_0, p2m_u_1} K V
      (@DivisionSemiring.toSemiring.{p2m_u_0} K
        (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
      (@AddCommGroup.toAddCommMonoid.{p2m_u_1} V inst_1)]
  {ι : Type p2m_u_2} {κ : Type p2m_u_3}
  (bank :
    ι →
      @Module.Dual.{p2m_u_0, p2m_u_1} K V
        (@DivisionSemiring.toSemiring.{p2m_u_0} K
          (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
        (@AddCommGroup.toAddCommMonoid.{p2m_u_1} V inst_1) inst_2)
  (selected : κ → ι),
  @Eq.{max (p2m_u_0 + 1) (p2m_u_1 + 1)}
      (@Submodule.{p2m_u_0, max p2m_u_0 p2m_u_1} K
        (@Module.Dual.{p2m_u_0, p2m_u_1} K V
          (@DivisionSemiring.toSemiring.{p2m_u_0} K
            (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
          (@AddCommGroup.toAddCommMonoid.{p2m_u_1} V inst_1) inst_2)
        (@DivisionSemiring.toSemiring.{p2m_u_0} K
          (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
        (@LinearMap.addCommMonoid.{p2m_u_0, p2m_u_0, p2m_u_1, p2m_u_0} K K V K
          (@DivisionSemiring.toSemiring.{p2m_u_0} K
            (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
          (@DivisionSemiring.toSemiring.{p2m_u_0} K
            (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
          (@AddCommGroup.toAddCommMonoid.{p2m_u_1} V inst_1)
          (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0} K
            (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0} K
              (@Semiring.toNonAssocSemiring.{p2m_u_0} K
                (@DivisionSemiring.toSemiring.{p2m_u_0} K
                  (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))))
          inst_2
          (@Semiring.toModule.{p2m_u_0} K
            (@DivisionSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))
          (@RingHom.id.{p2m_u_0} K
            (@Semiring.toNonAssocSemiring.{p2m_u_0} K
              (@DivisionSemiring.toSemiring.{p2m_u_0} K
                (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))))
        (@LinearMap.module.{p2m_u_0, p2m_u_0, p2m_u_0, p2m_u_1, p2m_u_0} K K K V K
          (@DivisionSemiring.toSemiring.{p2m_u_0} K
            (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
          (@DivisionSemiring.toSemiring.{p2m_u_0} K
            (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
          (@AddCommGroup.toAddCommMonoid.{p2m_u_1} V inst_1)
          (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0} K
            (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0} K
              (@Semiring.toNonAssocSemiring.{p2m_u_0} K
                (@DivisionSemiring.toSemiring.{p2m_u_0} K
                  (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))))
          inst_2
          (@Semiring.toModule.{p2m_u_0} K
            (@DivisionSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))
          (@RingHom.id.{p2m_u_0} K
            (@Semiring.toNonAssocSemiring.{p2m_u_0} K
              (@DivisionSemiring.toSemiring.{p2m_u_0} K
                (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))))
          (@DivisionSemiring.toSemiring.{p2m_u_0} K
            (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
          (@Semiring.toModule.{p2m_u_0} K
            (@DivisionSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))
          (@Algebra.to_smulCommClass.{p2m_u_0, p2m_u_0} K K
            (@Semifield.toCommSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))
            (@CommSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toCommSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
            (@Algebra.id.{p2m_u_0} K (@Semifield.toCommSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))))
      (@Submodule.span.{p2m_u_0, max p2m_u_0 p2m_u_1} K
        (@Module.Dual.{p2m_u_0, p2m_u_1} K V
          (@DivisionSemiring.toSemiring.{p2m_u_0} K
            (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
          (@AddCommGroup.toAddCommMonoid.{p2m_u_1} V inst_1) inst_2)
        (@DivisionSemiring.toSemiring.{p2m_u_0} K
          (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
        (@LinearMap.addCommMonoid.{p2m_u_0, p2m_u_0, p2m_u_1, p2m_u_0} K K V K
          (@DivisionSemiring.toSemiring.{p2m_u_0} K
            (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
          (@DivisionSemiring.toSemiring.{p2m_u_0} K
            (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
          (@AddCommGroup.toAddCommMonoid.{p2m_u_1} V inst_1)
          (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0} K
            (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0} K
              (@Semiring.toNonAssocSemiring.{p2m_u_0} K
                (@DivisionSemiring.toSemiring.{p2m_u_0} K
                  (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))))
          inst_2
          (@Semiring.toModule.{p2m_u_0} K
            (@DivisionSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))
          (@RingHom.id.{p2m_u_0} K
            (@Semiring.toNonAssocSemiring.{p2m_u_0} K
              (@DivisionSemiring.toSemiring.{p2m_u_0} K
                (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))))
        (@LinearMap.module.{p2m_u_0, p2m_u_0, p2m_u_0, p2m_u_1, p2m_u_0} K K K V K
          (@DivisionSemiring.toSemiring.{p2m_u_0} K
            (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
          (@DivisionSemiring.toSemiring.{p2m_u_0} K
            (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
          (@AddCommGroup.toAddCommMonoid.{p2m_u_1} V inst_1)
          (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0} K
            (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0} K
              (@Semiring.toNonAssocSemiring.{p2m_u_0} K
                (@DivisionSemiring.toSemiring.{p2m_u_0} K
                  (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))))
          inst_2
          (@Semiring.toModule.{p2m_u_0} K
            (@DivisionSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))
          (@RingHom.id.{p2m_u_0} K
            (@Semiring.toNonAssocSemiring.{p2m_u_0} K
              (@DivisionSemiring.toSemiring.{p2m_u_0} K
                (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))))
          (@DivisionSemiring.toSemiring.{p2m_u_0} K
            (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
          (@Semiring.toModule.{p2m_u_0} K
            (@DivisionSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))
          (@Algebra.to_smulCommClass.{p2m_u_0, p2m_u_0} K K
            (@Semifield.toCommSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))
            (@CommSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toCommSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
            (@Algebra.id.{p2m_u_0} K (@Semifield.toCommSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))))
        (@Set.range.{max p2m_u_0 p2m_u_1, p2m_u_3 + 1}
          (@Module.Dual.{p2m_u_0, p2m_u_1} K V
            (@DivisionSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
            (@AddCommGroup.toAddCommMonoid.{p2m_u_1} V inst_1) inst_2)
          κ
          (@Function.comp.{p2m_u_3 + 1, p2m_u_2 + 1, (max p2m_u_0 p2m_u_1) + 1} κ ι
            (@Module.Dual.{p2m_u_0, p2m_u_1} K V
              (@DivisionSemiring.toSemiring.{p2m_u_0} K
                (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
              (@AddCommGroup.toAddCommMonoid.{p2m_u_1} V inst_1) inst_2)
            bank selected)))
      (@Submodule.span.{p2m_u_0, max p2m_u_0 p2m_u_1} K
        (@Module.Dual.{p2m_u_0, p2m_u_1} K V
          (@DivisionSemiring.toSemiring.{p2m_u_0} K
            (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
          (@AddCommGroup.toAddCommMonoid.{p2m_u_1} V inst_1) inst_2)
        (@DivisionSemiring.toSemiring.{p2m_u_0} K
          (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
        (@LinearMap.addCommMonoid.{p2m_u_0, p2m_u_0, p2m_u_1, p2m_u_0} K K V K
          (@DivisionSemiring.toSemiring.{p2m_u_0} K
            (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
          (@DivisionSemiring.toSemiring.{p2m_u_0} K
            (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
          (@AddCommGroup.toAddCommMonoid.{p2m_u_1} V inst_1)
          (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0} K
            (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0} K
              (@Semiring.toNonAssocSemiring.{p2m_u_0} K
                (@DivisionSemiring.toSemiring.{p2m_u_0} K
                  (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))))
          inst_2
          (@Semiring.toModule.{p2m_u_0} K
            (@DivisionSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))
          (@RingHom.id.{p2m_u_0} K
            (@Semiring.toNonAssocSemiring.{p2m_u_0} K
              (@DivisionSemiring.toSemiring.{p2m_u_0} K
                (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))))
        (@LinearMap.module.{p2m_u_0, p2m_u_0, p2m_u_0, p2m_u_1, p2m_u_0} K K K V K
          (@DivisionSemiring.toSemiring.{p2m_u_0} K
            (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
          (@DivisionSemiring.toSemiring.{p2m_u_0} K
            (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
          (@AddCommGroup.toAddCommMonoid.{p2m_u_1} V inst_1)
          (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0} K
            (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0} K
              (@Semiring.toNonAssocSemiring.{p2m_u_0} K
                (@DivisionSemiring.toSemiring.{p2m_u_0} K
                  (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))))
          inst_2
          (@Semiring.toModule.{p2m_u_0} K
            (@DivisionSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))
          (@RingHom.id.{p2m_u_0} K
            (@Semiring.toNonAssocSemiring.{p2m_u_0} K
              (@DivisionSemiring.toSemiring.{p2m_u_0} K
                (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))))
          (@DivisionSemiring.toSemiring.{p2m_u_0} K
            (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
          (@Semiring.toModule.{p2m_u_0} K
            (@DivisionSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))
          (@Algebra.to_smulCommClass.{p2m_u_0, p2m_u_0} K K
            (@Semifield.toCommSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))
            (@CommSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toCommSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
            (@Algebra.id.{p2m_u_0} K (@Semifield.toCommSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))))
        (@Set.range.{max p2m_u_0 p2m_u_1, p2m_u_2 + 1}
          (@Module.Dual.{p2m_u_0, p2m_u_1} K V
            (@DivisionSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
            (@AddCommGroup.toAddCommMonoid.{p2m_u_1} V inst_1) inst_2)
          ι bank)) →
    (@Function.Injective.{p2m_u_1 + 1, max (p2m_u_0 + 1) (p2m_u_2 + 1)} V (ι → K) fun x i =>
        @DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_1 + 1, p2m_u_0 + 1}
          (@Module.Dual.{p2m_u_0, p2m_u_1} K V
            (@DivisionSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
            (@AddCommGroup.toAddCommMonoid.{p2m_u_1} V inst_1) inst_2)
          V (fun x => K)
          (@LinearMap.instFunLike.{p2m_u_0, p2m_u_0, p2m_u_1, p2m_u_0} K K V K
            (@DivisionSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
            (@DivisionSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
            (@AddCommGroup.toAddCommMonoid.{p2m_u_1} V inst_1)
            (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0} K
              (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0} K
                (@Semiring.toNonAssocSemiring.{p2m_u_0} K
                  (@DivisionSemiring.toSemiring.{p2m_u_0} K
                    (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))))
            inst_2
            (@Semiring.toModule.{p2m_u_0} K
              (@DivisionSemiring.toSemiring.{p2m_u_0} K
                (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))
            (@RingHom.id.{p2m_u_0} K
              (@Semiring.toNonAssocSemiring.{p2m_u_0} K
                (@DivisionSemiring.toSemiring.{p2m_u_0} K
                  (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))))
          (bank i) x) →
      @Function.Injective.{p2m_u_1 + 1, max (p2m_u_0 + 1) (p2m_u_3 + 1)} V (κ → K) fun x j =>
        @DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_1 + 1, p2m_u_0 + 1}
          (@Module.Dual.{p2m_u_0, p2m_u_1} K V
            (@DivisionSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
            (@AddCommGroup.toAddCommMonoid.{p2m_u_1} V inst_1) inst_2)
          V (fun x => K)
          (@LinearMap.instFunLike.{p2m_u_0, p2m_u_0, p2m_u_1, p2m_u_0} K K V K
            (@DivisionSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
            (@DivisionSemiring.toSemiring.{p2m_u_0} K
              (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst)))
            (@AddCommGroup.toAddCommMonoid.{p2m_u_1} V inst_1)
            (@NonUnitalNonAssocSemiring.toAddCommMonoid.{p2m_u_0} K
              (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{p2m_u_0} K
                (@Semiring.toNonAssocSemiring.{p2m_u_0} K
                  (@DivisionSemiring.toSemiring.{p2m_u_0} K
                    (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))))
            inst_2
            (@Semiring.toModule.{p2m_u_0} K
              (@DivisionSemiring.toSemiring.{p2m_u_0} K
                (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))
            (@RingHom.id.{p2m_u_0} K
              (@Semiring.toNonAssocSemiring.{p2m_u_0} K
                (@DivisionSemiring.toSemiring.{p2m_u_0} K
                  (@Semifield.toDivisionSemiring.{p2m_u_0} K (@Field.toSemifield.{p2m_u_0} K inst))))))
          (bank (selected j)) x := @_root_.Couret.STROBO2TORS.p2m_local_recoh_spanning_subbank_preserves_injectivity

