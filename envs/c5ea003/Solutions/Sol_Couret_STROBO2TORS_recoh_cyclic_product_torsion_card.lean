-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_product_torsion_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:26:47.243119+00:00
-- url     : https://prove2.me/submissions/41d4b604-8a79-4aab-9837-8f3df044126f

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



















































/-- A cyclic group has `gcd(n,p)` elements killed by `p`. -/
theorem recoh_cyclic_torsion_card (n p : ℕ) [NeZero n] :
    Nat.card (recohTorsionSubgroup (G := ZMod n) p) = n.gcd p := by
  change Nat.card (nsmulAddMonoidHom p : ZMod n →+ ZMod n).ker = _
  simpa only [Nat.card_eq_fintype_card, ZMod.card] using
    IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod n) p

/-- The actual `p`-torsion rank is the number of cyclic factors divisible
by `p`; no rank or cardinality hypothesis is supplied to this theorem. -/
theorem p2m_local_recoh_cyclic_product_torsion_card (p : ℕ) [Fact p.Prime] :
    Nat.card (recohTorsionSubgroup (G := (i : Fin d) → ZMod (q i)) p) =
      p ^ Fintype.card (RecohPrimaryCoordinate q p) := by
  rw [Nat.card_congr (recohProductTorsionEquiv q p), Nat.card_pi]
  simp_rw [recoh_cyclic_torsion_card]
  have hgcd : ∀ i : Fin d, (q i).gcd p = if p ∣ q i then p else 1 := by
    intro i
    by_cases hi : p ∣ q i
    · simpa only [if_pos hi] using (Nat.gcd_eq_right_iff_dvd.mpr hi)
    · rw [if_neg hi, Nat.gcd_comm]
      exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hi).gcd_eq_one
  simp_rw [hgcd]
  simp [Finset.prod_ite, Fintype.card_subtype]





end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat) [∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (p : Nat) [Fact (Nat.Prime p)],
  @Eq.{1} Nat
    (Nat.card.{0}
      (@Subtype.{1} ((i : Fin d) → ZMod (q i)) fun x =>
        @Membership.mem.{0, 0} ((i : Fin d) → ZMod (q i))
          (@AddSubgroup.{0} ((i : Fin d) → ZMod (q i))
            (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
              (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
          (@SetLike.instMembership.{0, 0}
            (@AddSubgroup.{0} ((i : Fin d) → ZMod (q i))
              (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                  @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
            ((i : Fin d) → ZMod (q i))
            (@AddSubgroup.instSetLike.{0} ((i : Fin d) → ZMod (q i))
              (@AddCommGroup.toAddGroup.{0} ((i : Fin d) → ZMod (q i))
                (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                  @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))
          (@Couret.STROBO2TORS.recohTorsionSubgroup.{0} ((i : Fin d) → ZMod (q i))
            (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
              @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
            p)
          x))
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid)) p
      (@Fintype.card.{0} (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q p)
        (@Subtype.fintype.{0} (Fin d) (fun i => @Dvd.dvd.{0} Nat Nat.instDvd p (q i))
          (fun a => Nat.decidable_dvd p (q a)) (Fin.fintype d)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_product_torsion_card

