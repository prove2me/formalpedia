-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_square_injective_of_no_even
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:53:47.454205+00:00
-- url     : https://prove2.me/submissions/f15ab63f-0ed2-4dd1-8634-6d9a7ef10ed6

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_primary_bank_separates
import Theorems.Thm_Couret_STROBO2TORS_recoh_square_injective_of_trivial_two_torsion
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

























































/-- Without an even cyclic factor the labelled square alone is injective
on triple supports, so no ternary slots are necessary. -/
theorem p2m_local_recoh_cyclic_square_injective_of_no_even
    (hodd : ∀ i : Fin d, ¬ 2 ∣ q i) :
    Function.Injective
      (fun S : {S : Finset ((j : Fin d) → ZMod (q j)) // S.card = 3} =>
        orderedSquare S.1) := by
  apply recoh_square_injective_of_trivial_two_torsion
  intro u hu
  apply recoh_cyclic_primary_bank_separates q 2 (recohCanonicalPrimaryData q 2) u
  · simpa only [two_nsmul] using hu
  · intro i
    exact (hodd i.val i.property).elim

end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)],
  (∀ (i : Fin d),
      Not (@Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q i))) →
    @Function.Injective.{1, 1}
      (@Subtype.{1} (Finset.{0} ((j : Fin d) → ZMod (q j))) fun S =>
        @Eq.{1} Nat (@Finset.card.{0} ((j : Fin d) → ZMod (q j)) S)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (((j : Fin d) → ZMod (q j)) → Nat) fun S =>
      @Couret.STROBO2TORS.orderedSquare.{0} ((j : Fin d) → ZMod (q j))
        (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
          @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
        (fun a b =>
          @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
            (Fin.fintype d) a b)
        (@Subtype.val.{1} (Finset.{0} ((j : Fin d) → ZMod (q j)))
          (fun S =>
            @Eq.{1} Nat (@Finset.card.{0} ((j : Fin d) → ZMod (q j)) S)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_square_injective_of_no_even

