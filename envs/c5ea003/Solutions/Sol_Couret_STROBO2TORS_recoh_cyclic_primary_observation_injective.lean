-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_primary_observation_injective
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:26:43.149278+00:00
-- url     : https://prove2.me/submissions/d8bcbe43-ca04-4001-bd83-a917016f60f9

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_binary_probe_nonzero
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_primary_bank_separates
import Theorems.Thm_Couret_STROBO2TORS_recoh_observation_injective_of_separating_banks
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















































/-- The explicit binary and ternary coordinate bank reconstructs triples.
No abstract separation, nonvanishing or encoding hypothesis is needed. -/
theorem p2m_local_recoh_cyclic_primary_observation_injective
    (data2 : RecohPrimaryFactorData q 2) (data3 : RecohPrimaryFactorData q 3) :
    Function.Injective (fun S : {S : Finset ((j : Fin d) → ZMod (q j)) // S.card = 3} =>
      recohObservation
        (Sum.elim (recohCyclicPrimaryBank q 2 data2) (recohCyclicPrimaryBank q 3 data3)) S.1) := by
  apply recoh_observation_injective_of_separating_banks
  · exact recoh_cyclic_binary_probe_nonzero q data2
  · intro u hu hbank
    apply recoh_cyclic_primary_bank_separates q 2 data2 u _ hbank
    simpa only [two_nsmul] using hu
  · exact recoh_cyclic_ternary_bank_trivial_on_two q data3
  · intro v hv hbank
    apply recoh_cyclic_primary_bank_separates q 3 data3 v _ hbank
    simpa only [succ_nsmul, zero_nsmul, zero_add] using hv











end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat) [∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (data2 : @Couret.STROBO2TORS.RecohPrimaryFactorData d q (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (data3 :
    @Couret.STROBO2TORS.RecohPrimaryFactorData d q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))),
  @Function.Injective.{1, 1}
    (@Subtype.{1} (Finset.{0} ((j : Fin d) → ZMod (q j))) fun S =>
      @Eq.{1} Nat (@Finset.card.{0} ((j : Fin d) → ZMod (q j)) S)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (Prod.{0, 0} (((j : Fin d) → ZMod (q j)) → Nat)
      (Sum.{0, 0}
          (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
        Complex))
    fun S =>
    @Couret.STROBO2TORS.recohObservation.{0, 0} ((j : Fin d) → ZMod (q j))
      (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
        @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
      (fun a b =>
        @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
          (Fin.fintype d) a b)
      (Sum.{0, 0}
        (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@Sum.elim.{0, 0, 1}
        (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@AddChar.{0, 0} ((j : Fin d) → ZMod (q j))
          (@SubNegMonoid.toAddMonoid.{0} ((j : Fin d) → ZMod (q j))
            (@AddGroup.toSubNegMonoid.{0} ((j : Fin d) → ZMod (q j))
              (@AddCommGroup.toAddGroup.{0} ((j : Fin d) → ZMod (q j))
                (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                  @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))
          Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
        (@Couret.STROBO2TORS.recohCyclicPrimaryBank d q (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          Nat.fact_prime_two data2)
        (@Couret.STROBO2TORS.recohCyclicPrimaryBank d q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          Nat.fact_prime_three data3))
      (@Subtype.val.{1} (Finset.{0} ((j : Fin d) → ZMod (q j)))
        (fun S =>
          @Eq.{1} Nat (@Finset.card.{0} ((j : Fin d) → ZMod (q j)) S)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_primary_observation_injective

