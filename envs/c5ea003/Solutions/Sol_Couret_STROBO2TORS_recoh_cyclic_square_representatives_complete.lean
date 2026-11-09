-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_square_representatives_complete
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:56:52.938298+00:00
-- url     : https://prove2.me/submissions/3336ff51-7963-4b8e-b3c4-90c544d4ffea

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

























theorem p2m_local_recoh_cyclic_square_representatives_complete
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hsquare : orderedSquare S = recohTypedSquareValue entries) :
    ∃ B ∈ recohCyclicSquareRepresentatives q entries, OrdinaryPartner B S :=
  recoh_square_representatives_complete _ _ _ (recoh_product_half_spec q)
    (recoh_selected_square_support_covered q entries) S hS hsquare











end Cyclic

end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat) [∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat)) (S : Finset.{0} ((i : Fin d) → ZMod (q i))),
  @Eq.{1} Nat (@Finset.card.{0} ((i : Fin d) → ZMod (q i)) S)
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
      @Exists.{1} (Finset.{0} ((i : Fin d) → ZMod (q i))) fun B =>
        And
          (@Membership.mem.{0, 0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
            (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
            (@SetLike.instMembership.{0, 0} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
              (Finset.{0} ((i : Fin d) → ZMod (q i))) (@Finset.instSetLike.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))))
            (@Couret.STROBO2TORS.recohCyclicSquareRepresentatives d q entries) B)
          (@Couret.STROBO2TORS.OrdinaryPartner.{0} ((i : Fin d) → ZMod (q i))
            (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
              @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            B S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_square_representatives_complete

