-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_primary_bank_separates
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:02:41.783878+00:00
-- url     : https://prove2.me/submissions/d818e502-dce8-41da-8422-915170d074a7

import Aesop
import Definitions.Def_Couret_RecohCyclicPrimaryBank_92b8732c410a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_primary_coordinate_kernel
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Definitions.Def_Couret_RecohSignRecovery_71a8a4a1ce8a
import Definitions.Def_Couret_RecohCyclicCoordinates_d669b2caaf1a
import Mathlib.Data.Multiset.Sort
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option autoImplicit false

/-!
Coordinate primary characters and executable exponent encodings for finite
products of cyclic groups. The encoding sorts the multiset of coordinate
values, so multiplicities are retained and no enumeration of the ambient
group is used. Complex roots and characters are semantic objects; exponent
lists and primary-factor data are the inputs used by the exact backend.
-/

namespace Couret.STROBO2TORS





variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]









































/-- The bank has one labelled slot for every factor divisible by `p`, and
these slots separate the actual subgroup killed by `p`. -/
theorem p2m_local_recoh_cyclic_primary_bank_separates (p : ℕ) [Fact p.Prime]
    (data : RecohPrimaryFactorData q p)
    (x : (j : Fin d) → ZMod (q j)) (hx : p • x = 0)
    (hbank : ∀ i, recohCyclicPrimaryBank q p data i x = 1) : x = 0 := by
  funext i
  have hxi : p • x i = 0 := by
    simpa only [Pi.smul_apply, Pi.zero_apply] using congrFun hx i
  by_cases hi : p ∣ q i
  · exact (recoh_cyclic_primary_coordinate_kernel q p data ⟨i, hi⟩ x hxi).mp
      (hbank ⟨i, hi⟩)
  · exact recoh_cyclic_torsion_zero_of_coprime p (q i)
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hi) (x i) hxi

















end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat) [∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (p : Nat) [inst : Fact (Nat.Prime p)] (data : @Couret.STROBO2TORS.RecohPrimaryFactorData d q p)
  (x : (j : Fin d) → ZMod (q j)),
  @Eq.{1} ((j : Fin d) → ZMod (q j))
      (@HSMul.hSMul.{0, 0, 0} Nat ((j : Fin d) → ZMod (q j)) ((j : Fin d) → ZMod (q j))
        (@instHSMul.{0, 0} Nat ((j : Fin d) → ZMod (q j))
          (@AddMonoid.toNSMul.{0} ((j : Fin d) → ZMod (q j))
            (@Pi.addMonoid.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
              @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
                  (@Ring.toAddGroupWithOne.{0} (ZMod (q i))
                    (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))))
        p x)
      (@OfNat.ofNat.{0} ((j : Fin d) → ZMod (q j)) (nat_lit 0)
        (@Zero.toOfNat0.{0} ((j : Fin d) → ZMod (q j))
          (@Pi.instZero.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
            @MulZeroClass.toZero.{0} (ZMod (q i))
              (@instMulZeroClassOfSemiring.{0} (ZMod (q i))
                (@CommSemiring.toSemiring.{0} (ZMod (q i))
                  (@CommRing.toCommSemiring.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))) →
    (∀ (i : @Couret.STROBO2TORS.RecohPrimaryCoordinate d q p),
        @Eq.{1} Complex
          (@DFunLike.coe.{1, 1, 1}
            (@AddChar.{0, 0} ((j : Fin d) → ZMod (q j))
              (@Pi.addMonoid.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
                    (@Ring.toAddGroupWithOne.{0} (ZMod (q i))
                      (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
              Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
            ((j : Fin d) → ZMod (q j)) (fun x => Complex)
            (@AddChar.instFunLike.{0, 0} ((j : Fin d) → ZMod (q j)) Complex
              (@Pi.addMonoid.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
                    (@Ring.toAddGroupWithOne.{0} (ZMod (q i))
                      (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
              (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
            (@Couret.STROBO2TORS.recohCyclicPrimaryBank d q p inst data i) x)
          (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
      @Eq.{1} ((j : Fin d) → ZMod (q j)) x
        (@OfNat.ofNat.{0} ((j : Fin d) → ZMod (q j)) (nat_lit 0)
          (@Zero.toOfNat0.{0} ((j : Fin d) → ZMod (q j))
            (@Pi.instZero.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
              @MulZeroClass.toZero.{0} (ZMod (q i))
                (@instMulZeroClassOfSemiring.{0} (ZMod (q i))
                  (@CommSemiring.toSemiring.{0} (ZMod (q i))
                    (@CommRing.toCommSemiring.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_primary_bank_separates

