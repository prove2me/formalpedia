-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_indexed_recover_support_square
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:28:01.677573+00:00
-- url     : https://prove2.me/submissions/50bc2198-d2e1-4e88-80e1-57f872868589

import Aesop
import Definitions.Def_Couret_RecohPreparedDecoder_2b97e051dec5
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
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCoefficientDecoder_a5265698d3d8

set_option autoImplicit false

/-!
Move the square test before sign recovery, as in Python `_prepare_square`.

The generic prepared decoder filters the chosen representatives before
recovery and retains the complete final checker after recovery.  The two
orders give the same answer whenever a final acceptance implies acceptance
of the representative by the precheck.  For the square test, this implication
follows from invariance under every two-torsion translation, for all finite
supports.  The resulting coefficient backend is therefore equal to the
previously certified backend, under the same support-coverage contract.

This module certifies an order of mathematical operations.  It does not
certify the separate Python cache, parser, or runtime.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



















variable {J : Type*}

local notation "H₂" => recohTorsionSubgroup (G := G) 2

/-- Boolean sign recovery always translates by an element of G[2], even
when the supplied observations will ultimately be rejected. -/
theorem p2m_local_recoh_indexed_recover_support_square
    (e : H₂ ≃+ (J → ZMod 2)) (same : Finset G → J → Bool) (B : Finset G) :
    orderedSquare (recohIndexedRecoverSupport e same B) = orderedSquare B := by
  apply recoh_ordered_square_two_torsion_translate
  simpa only [recoh_mem_torsion_subgroup, two_nsmul] using
    (recohIndexedRecoverTranslation e (same B)).property



variable {I : Type*} [Fintype I]







end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] {J : Type p2m_u_1}
  (e :
    @AddEquiv.{p2m_u_0, p2m_u_1}
      (@Subtype.{p2m_u_0 + 1} G fun x =>
        @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
            (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
            (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
          (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          x)
      (J → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
        (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@Pi.instAdd.{p2m_u_1, 0} J (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
        @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Semifield.toDivisionSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    Nat.fact_prime_two)))))))
  (same : Finset.{p2m_u_0} G → J → Bool) (B : Finset.{p2m_u_0} G),
  @Eq.{p2m_u_0 + 1} (G → Nat)
    (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
      (@Couret.STROBO2TORS.recohIndexedRecoverSupport.{p2m_u_0, p2m_u_1} G J inst inst_1 e same B))
    (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 B) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_indexed_recover_support_square

