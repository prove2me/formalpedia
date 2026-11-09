-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_square_selected_orbits
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:11:13.643954+00:00
-- url     : https://prove2.me/submissions/e3325003-8806-49f4-9ae8-1d00857cb24d

import Aesop
import Definitions.Def_Couret_RecohSquareSelector_3b7a2954c02a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
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
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_square_representatives_complete
import Theorems.Thm_Couret_STROBO2TORS_recoh_square_ternary_choice_complete
import Definitions.Def_Couret_RecohCyclicPreparedDecoder_0ae8cdf0a932
import Definitions.Def_Couret_RecohTernaryFibreSelector_4c0db0f29983

set_option autoImplicit false

/-!
Selection from the labelled ordered square using at most twenty explicit
representatives. All runtime checks use finite supports, cyclic coordinates
and integer cyclotomic coefficients. No ambient-group search occurs.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























variable [Fintype G]



section FiniteSelection

variable {α : Type*}







end FiniteSelection

section Cyclic

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

































/-- Equality of the selected ternary reading forces two supports with the
observed square into the same two-torsion orbit. In the ordinary case the
premise has no measurement slots. -/
theorem p2m_local_recoh_square_selected_orbits
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (S T : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3) (hT : T.card = 3)
    (hSR : orderedSquare S = recohTypedSquareValue entries)
    (hTR : orderedSquare T = recohTypedSquareValue entries)
    (hread : ∀ j, recohSquareTernaryChoice q entries = some j →
      recohSupportProbe (recohCyclicPrimaryBank q 3 (recohCanonicalPrimaryData q 3) j) S =
        recohSupportProbe (recohCyclicPrimaryBank q 3 (recohCanonicalPrimaryData q 3) j) T) :
    OrdinaryPartner S T := by
  obtain ⟨B, hB, hBS⟩ := recoh_cyclic_square_representatives_complete q entries S hS hSR
  obtain ⟨C, hC, hCT⟩ := recoh_cyclic_square_representatives_complete q entries T hT hTR
  have hBC : OrdinaryPartner B C := by
    have hnonempty := recoh_cyclic_square_representatives_nonempty q entries
    rcases recoh_square_ternary_choice_complete q entries S hS hSR with ho | ⟨j, hj, hp⟩
    · exact ((recoh_one_orbit_check_iff _ hnonempty).mp ho) B hB C hC
    · apply ((recoh_ternary_orbit_check_iff q _ hnonempty j).mp hp) B hB C hC
      calc
        recohSupportProbe (recohCyclicPrimaryBank q 3 (recohCanonicalPrimaryData q 3) j) B =
            recohSupportProbe (recohCyclicPrimaryBank q 3 (recohCanonicalPrimaryData q 3) j) S :=
          recoh_cyclic_ternary_constant_on_ordinary q _ j B S hBS
        _ = recohSupportProbe (recohCyclicPrimaryBank q 3 (recohCanonicalPrimaryData q 3) j) T :=
          hread j hj
        _ = recohSupportProbe (recohCyclicPrimaryBank q 3 (recohCanonicalPrimaryData q 3) j) C :=
          (recoh_cyclic_ternary_constant_on_ordinary q _ j C T hCT).symm
  exact recoh_ordinary_partner_trans
    (recoh_ordinary_partner_trans (recoh_ordinary_partner_symm hBS) hBC) hCT



end Cyclic

end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat)) (S T : Finset.{0} ((i : Fin d) → ZMod (q i))),
  @Eq.{1} Nat (@Finset.card.{0} ((i : Fin d) → ZMod (q i)) S)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{1} Nat (@Finset.card.{0} ((i : Fin d) → ZMod (q i)) T)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      @Eq.{1} (((i : Fin d) → ZMod (q i)) → Nat)
          (@Couret.STROBO2TORS.orderedSquare.{0} ((i : Fin d) → ZMod (q i))
            (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
              @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            S)
          (@Couret.STROBO2TORS.recohTypedSquareValue.{0} ((i : Fin d) → ZMod (q i))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            entries) →
        @Eq.{1} (((i : Fin d) → ZMod (q i)) → Nat)
            (@Couret.STROBO2TORS.orderedSquare.{0} ((i : Fin d) → ZMod (q i))
              (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
              (fun a b =>
                @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                  (Fin.fintype d) a b)
              T)
            (@Couret.STROBO2TORS.recohTypedSquareValue.{0} ((i : Fin d) → ZMod (q i))
              (fun a b =>
                @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                  (Fin.fintype d) a b)
              entries) →
          (∀
              (j :
                @Couret.STROBO2TORS.RecohPrimaryCoordinate d q
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))),
              @Eq.{1}
                  (Option.{0}
                    (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (@Couret.STROBO2TORS.recohSquareTernaryChoice d q inst entries)
                  (@Option.some.{0}
                    (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    j) →
                @Eq.{1} Complex
                  (@Couret.STROBO2TORS.recohSupportProbe.{0} ((j : Fin d) → ZMod (q j))
                    (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                      @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                    (@Couret.STROBO2TORS.recohCyclicPrimaryBank d q
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Nat.fact_prime_three
                      (@Couret.STROBO2TORS.recohCanonicalPrimaryData d q inst
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Nat.fact_prime_three)
                      j)
                    S)
                  (@Couret.STROBO2TORS.recohSupportProbe.{0} ((j : Fin d) → ZMod (q j))
                    (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                      @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                    (@Couret.STROBO2TORS.recohCyclicPrimaryBank d q
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Nat.fact_prime_three
                      (@Couret.STROBO2TORS.recohCanonicalPrimaryData d q inst
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Nat.fact_prime_three)
                      j)
                    T)) →
            @Couret.STROBO2TORS.OrdinaryPartner.{0} ((i : Fin d) → ZMod (q i))
              (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
              (fun a b =>
                @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                  (Fin.fintype d) a b)
              S T := @_root_.Couret.STROBO2TORS.p2m_local_recoh_square_selected_orbits

