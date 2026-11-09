-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_ternary_selected_detects
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:51:16.598652+00:00
-- url     : https://prove2.me/submissions/2148543a-7a65-48dd-b411-d4a9068b69f8

import Aesop
import Definitions.Def_Couret_RecohTernarySelector_13a2b1134dfc
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
import Definitions.Def_Couret_RecohCyclicPrimaryBank_92b8732c410a

set_option autoImplicit false

/-!
An executable coordinate selector for a supplied direction killed by three.
The search visits the labelled cyclic coordinates in increasing order and
returns the first nonzero coordinate whose modulus is divisible by three.
Only natural divisibility and equality in a cyclic group are tested.

The optional selector is defined on every input vector. The total selector
requires the direction to be nonzero and killed by three; its proof arguments
are erased during execution. Complex characters are used only to state the
semantic detection guarantee for the selected coordinate.
-/

namespace Couret.STROBO2TORS

variable {d : ℕ} (q : Fin d → ℕ)











theorem recoh_ternary_coordinate_scan_some_nonzero
    (v : (i : Fin d) → ZMod (q i)) (labels : List (Fin d))
    (i : RecohPrimaryCoordinate q 3)
    (hs : recohTernaryCoordinateScan q v labels = some i) :
    v i.val ≠ 0 := by
  induction labels with
  | nil => simp [recohTernaryCoordinateScan] at hs
  | cons j rest ih =>
      by_cases h : 3 ∣ q j ∧ v j ≠ 0
      · have heq : (⟨j, h.1⟩ : RecohPrimaryCoordinate q 3) = i :=
          Option.some.inj (by simpa only [recohTernaryCoordinateScan, dif_pos h] using hs)
        cases heq
        exact h.2
      · exact ih (by simpa only [recohTernaryCoordinateScan, dif_neg h] using hs)







theorem recoh_ternary_coordinate_some_nonzero
    (v : (i : Fin d) → ZMod (q i)) (i : RecohPrimaryCoordinate q 3)
    (hs : recohTernaryCoordinate? q v = some i) : v i.val ≠ 0 :=
  recoh_ternary_coordinate_scan_some_nonzero q v (List.finRange d) i hs









variable [∀ i, NeZero (q i)]







theorem recoh_ternary_coordinate_eq_some_selected
    (v : (i : Fin d) → ZMod (q i)) (hv : 3 • v = 0) (hv0 : v ≠ 0) :
    recohTernaryCoordinate? q v = some (recohTernaryCoordinate q v hv hv0) :=
  (Option.some_get _).symm





/-- Every successful output supplies a character detecting the direction. -/
theorem recoh_ternary_coordinate_some_detects
    (data3 : RecohPrimaryFactorData q 3)
    (v : (i : Fin d) → ZMod (q i)) (hv : 3 • v = 0)
    (i : RecohPrimaryCoordinate q 3)
    (hs : recohTernaryCoordinate? q v = some i) :
    recohCyclicPrimaryBank q 3 data3 i v ≠ 1 := by
  have hvi : 3 • v i.val = 0 := by
    simpa only [Pi.smul_apply, Pi.zero_apply] using congrFun hv i.val
  intro hone
  exact recoh_ternary_coordinate_some_nonzero q v i hs
    ((recoh_cyclic_primary_coordinate_kernel q 3 data3 i v hvi).mp hone)

theorem p2m_local_recoh_ternary_selected_detects
    (data3 : RecohPrimaryFactorData q 3)
    (v : (i : Fin d) → ZMod (q i)) (hv : 3 • v = 0) (hv0 : v ≠ 0) :
    recohCyclicPrimaryBank q 3 data3 (recohTernaryCoordinate q v hv hv0) v ≠ 1 :=
  recoh_ternary_coordinate_some_detects q data3 v hv _
    (recoh_ternary_coordinate_eq_some_selected q v hv hv0)





end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (data3 : @Couret.STROBO2TORS.RecohPrimaryFactorData d q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (v : (i : Fin d) → ZMod (q i))
  (hv :
    @Eq.{1} ((i : Fin d) → ZMod (q i))
      (@HSMul.hSMul.{0, 0, 0} Nat ((i : Fin d) → ZMod (q i)) ((i : Fin d) → ZMod (q i))
        (@instHSMul.{0, 0} Nat ((i : Fin d) → ZMod (q i))
          (@AddMonoid.toNSMul.{0} ((i : Fin d) → ZMod (q i))
            (@Pi.addMonoid.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
              @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
                  (@Ring.toAddGroupWithOne.{0} (ZMod (q i))
                    (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) v)
      (@OfNat.ofNat.{0} ((i : Fin d) → ZMod (q i)) (nat_lit 0)
        (@Zero.toOfNat0.{0} ((i : Fin d) → ZMod (q i))
          (@Pi.instZero.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
            @MulZeroClass.toZero.{0} (ZMod (q i))
              (@instMulZeroClassOfSemiring.{0} (ZMod (q i))
                (@CommSemiring.toSemiring.{0} (ZMod (q i))
                  (@CommRing.toCommSemiring.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))))
  (hv0 :
    @Ne.{1} ((i : Fin d) → ZMod (q i)) v
      (@OfNat.ofNat.{0} ((i : Fin d) → ZMod (q i)) (nat_lit 0)
        (@Zero.toOfNat0.{0} ((i : Fin d) → ZMod (q i))
          (@Pi.instZero.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
            @MulZeroClass.toZero.{0} (ZMod (q i))
              (@instMulZeroClassOfSemiring.{0} (ZMod (q i))
                (@CommSemiring.toSemiring.{0} (ZMod (q i))
                  (@CommRing.toCommSemiring.{0} (ZMod (q i)) (ZMod.commRing (q i))))))))),
  @Ne.{1} Complex
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
      (@Couret.STROBO2TORS.recohCyclicPrimaryBank d q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        Nat.fact_prime_three data3 (@Couret.STROBO2TORS.recohTernaryCoordinate d q inst v hv hv0))
      v)
    (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_ternary_selected_detects

