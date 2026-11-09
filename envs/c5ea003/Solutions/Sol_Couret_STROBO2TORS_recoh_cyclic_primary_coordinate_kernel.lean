-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_primary_coordinate_kernel
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:52.802211+00:00
-- url     : https://prove2.me/submissions/24d261f9-2814-4f3b-a0dc-fd3ad84ce14c

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





































/-- On `p`-torsion a full `p`-primary coordinate character has trivial
kernel, although it may have a nontrivial kernel on the full cyclic group. -/
theorem p2m_local_recoh_cyclic_primary_coordinate_kernel (p : ℕ) [Fact p.Prime]
    (data : RecohPrimaryFactorData q p) (i : RecohPrimaryCoordinate q p)
    (x : (j : Fin d) → ZMod (q j)) (hx : p • x i.val = 0) :
    recohCyclicPrimaryBank q p data i x = 1 ↔ x i.val = 0 := by
  let N := p ^ (data.exponent i + 1)
  letI : NeZero N := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  change recohCyclicCoordinateCharacter q i.val N _ x = 1 ↔ _
  rw [recoh_cyclic_coordinate_character_apply,
    (recoh_cyclic_root_primitive N).pow_eq_one_iff_dvd]
  constructor
  · intro hN
    have hq := recoh_cyclic_nsmul_zero_dvd p (q i.val) (x i.val) hx
    have hc : data.cofactor i ∣ p * (x i.val).val := by
      apply dvd_trans (show data.cofactor i ∣ q i.val from ?_) hq
      rw [data.factor i]
      exact dvd_mul_left _ _
    have hc' : data.cofactor i ∣ (x i.val).val :=
      (data.coprime i).symm.dvd_of_dvd_mul_left hc
    have hq' : q i.val ∣ (x i.val).val := by
      have hprod := ((data.coprime i).pow_left (data.exponent i + 1)).mul_dvd_of_dvd_of_dvd hN hc'
      exact dvd_trans (dvd_of_eq (data.factor i)) hprod
    exact (ZMod.natCast_zmod_val (x i.val)).symm.trans
      ((ZMod.natCast_eq_zero_iff _ _).mpr hq')
  · intro hzero
    simp only [hzero, ZMod.val_zero, dvd_zero]





















end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat) [∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (p : Nat) [inst : Fact (Nat.Prime p)] (data : @Couret.STROBO2TORS.RecohPrimaryFactorData d q p)
  (i : @Couret.STROBO2TORS.RecohPrimaryCoordinate d q p) (x : (j : Fin d) → ZMod (q j)),
  @Eq.{1} (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
      (@HSMul.hSMul.{0, 0, 0} Nat
        (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
        (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
        (@instHSMul.{0, 0} Nat (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
          (@AddMonoid.toNSMul.{0}
            (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
            (@AddMonoidWithOne.toAddMonoid.{0}
              (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
              (@AddGroupWithOne.toAddMonoidWithOne.{0}
                (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
                (@Ring.toAddGroupWithOne.{0}
                  (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
                  (@CommRing.toRing.{0}
                    (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
                    (ZMod.commRing
                      (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))))))))
        p (x (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
      (@OfNat.ofNat.{0} (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
        (nat_lit 0)
        (@Zero.toOfNat0.{0} (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
          (@MulZeroClass.toZero.{0}
            (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
            (@instMulZeroClassOfSemiring.{0}
              (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
              (@CommSemiring.toSemiring.{0}
                (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
                (@CommRing.toCommSemiring.{0}
                  (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
                  (ZMod.commRing
                    (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i))))))))) →
    Iff
      (@Eq.{1} Complex
        (@DFunLike.coe.{1, 1, 1}
          (@AddChar.{0, 0} ((j : Fin d) → ZMod (q j))
            (@Pi.addMonoid.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
              @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
                  (@Ring.toAddGroupWithOne.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
            Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
          ((j : Fin d) → ZMod (q j)) (fun x => Complex)
          (@AddChar.instFunLike.{0, 0} ((j : Fin d) → ZMod (q j)) Complex
            (@Pi.addMonoid.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
              @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
                  (@Ring.toAddGroupWithOne.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
            (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
          (@Couret.STROBO2TORS.recohCyclicPrimaryBank d q p inst data i) x)
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
      (@Eq.{1} (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
        (x (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i))
        (@OfNat.ofNat.{0} (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
          (nat_lit 0)
          (@Zero.toOfNat0.{0} (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
            (@MulZeroClass.toZero.{0}
              (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
              (@instMulZeroClassOfSemiring.{0}
                (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
                (@CommSemiring.toSemiring.{0}
                  (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
                  (@CommRing.toCommSemiring.{0}
                    (ZMod (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))
                    (ZMod.commRing
                      (q (@Subtype.val.{1} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i)) i)))))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_primary_coordinate_kernel

