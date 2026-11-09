-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_square_ternary_choice_none_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:29:18.23902+00:00
-- url     : https://prove2.me/submissions/77ba2fc9-924a-4799-ae15-63bad80f0f17

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_ordinary_partner_of_common_torsion_orbit
import Theorems.Thm_Couret_STROBO2TORS_recoh_square_selected_orbits
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_card
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_subset_fibre
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



































/-- The selector requests no ternary measurement exactly on the ordinary
fibres. Hence no redundant ternary measurement is requested there. -/
theorem p2m_local_recoh_square_ternary_choice_none_iff
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hsquare : orderedSquare S = recohTypedSquareValue entries) :
    recohSquareTernaryChoice q entries = none ↔
      (squareFibre S).card = (twoTorsion : Finset ((i : Fin d) → ZMod (q i))).card := by
  constructor
  · intro hnone
    have hsub : squareFibre S ⊆ torsionOrbit S := by
      intro T hT
      obtain ⟨hT3, hST⟩ := (mem_squareFibre S T).mp hT
      apply (mem_torsionOrbit S T).mpr
      apply recoh_square_selected_orbits q entries S T hS hT3 hsquare
        ((funext hST).symm.trans hsquare)
      intro j hj
      rw [hnone] at hj
      cases hj
    have heq := Finset.Subset.antisymm hsub (torsionOrbit_subset_fibre S hS)
    rw [heq, torsionOrbit_card S hS]
  · intro hcard
    have hfibre : squareFibre S = torsionOrbit S := by
      apply (Finset.eq_of_subset_of_card_le (torsionOrbit_subset_fibre S hS) ?_).symm
      rw [hcard, torsionOrbit_card S hS]
    have hrep : ∀ B ∈ recohCyclicSquareRepresentatives q entries, B ∈ torsionOrbit S := by
      intro B hB
      obtain ⟨hB3, hBR⟩ := recoh_cyclic_square_representatives_sound q entries B hB
      rw [← hfibre]
      exact (mem_squareFibre S B).mpr
        ⟨hB3, fun z => congrFun (hsquare.trans hBR.symm) z⟩
    have hone : recohOneOrbitCheck (recohCyclicSquareRepresentatives q entries) = true := by
      apply (recoh_one_orbit_check_iff _
        (recoh_cyclic_square_representatives_nonempty q entries)).mpr
      intro B hB C hC
      exact recoh_ordinary_partner_of_common_torsion_orbit S B C (hrep B hB) (hrep C hC)
    simp only [recohSquareTernaryChoice, hone, if_true]

end Cyclic

end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
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
      Iff
        (@Eq.{1}
          (Option.{0}
            (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (@Couret.STROBO2TORS.recohSquareTernaryChoice d q inst entries)
          (@Option.none.{0}
            (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
        (@Eq.{1} Nat
          (@Finset.card.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
            (@Couret.STROBO2TORS.squareFibre.{0} ((i : Fin d) → ZMod (q i))
              (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
              (fun a b =>
                @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                  (Fin.fintype d) a b)
              (@Pi.instFintype.{0, 0} (Fin d) (fun i => ZMod (q i)) (instDecidableEqFin d) (Fin.fintype d) fun a =>
                @ZMod.fintype (q a) (inst a))
              S))
          (@Finset.card.{0} ((i : Fin d) → ZMod (q i))
            (@Couret.STROBO2TORS.twoTorsion.{0} ((i : Fin d) → ZMod (q i))
              (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
              (fun a b =>
                @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                  (Fin.fintype d) a b)
              (@Pi.instFintype.{0, 0} (Fin d) (fun i => ZMod (q i)) (instDecidableEqFin d) (Fin.fintype d) fun a =>
                @ZMod.fintype (q a) (inst a))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_square_ternary_choice_none_iff

