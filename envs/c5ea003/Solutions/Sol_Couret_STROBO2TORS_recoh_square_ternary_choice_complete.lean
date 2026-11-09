-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_square_ternary_choice_complete
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:06:01.253179+00:00
-- url     : https://prove2.me/submissions/7a2dedab-36be-48d5-afb5-b8afc2df2515

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_fibre_orbit_separator
import Theorems.Thm_Couret_STROBO2TORS_recoh_first_passing_exists
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



theorem recoh_first_passing_sound (test : α → Bool) (xs : List α) (a : α)
    (h : recohFirstPassing test xs = some a) : test a = true := by
  induction xs with
  | nil => simp [recohFirstPassing] at h
  | cons b xs ih =>
    by_cases hb : test b = true
    · simp only [recohFirstPassing, hb, if_true, Option.some.injEq] at h
      simpa only [← h] using hb
    · simp only [recohFirstPassing, if_neg hb] at h
      exact ih h



end FiniteSelection

section Cyclic

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]































/-- On every realizable square the finite search either certifies one
orbit or finds a common separating ternary coordinate. -/
theorem p2m_local_recoh_square_ternary_choice_complete
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hsquare : orderedSquare S = recohTypedSquareValue entries) :
    recohOneOrbitCheck (recohCyclicSquareRepresentatives q entries) = true ∨
      ∃ j, recohSquareTernaryChoice q entries = some j ∧
        recohTernaryOrbitCheck q (recohCyclicSquareRepresentatives q entries) j = true := by
  let reps := recohCyclicSquareRepresentatives q entries
  have hnonempty : ∀ B ∈ reps, B.Nonempty :=
    recoh_cyclic_square_representatives_nonempty q entries
  have hfibre : ∀ B ∈ reps, B ∈ squareFibre S := by
    intro B hB
    obtain ⟨hB3, hBR⟩ := recoh_cyclic_square_representatives_sound q entries B hB
    exact (mem_squareFibre S B).mpr
      ⟨hB3, fun z => congrFun (hsquare.trans hBR.symm) z⟩
  by_cases ho : recohOneOrbitCheck reps = true
  · exact Or.inl ho
  · obtain ⟨j, hj⟩ : ∃ j, recohTernaryOrbitCheck q reps j = true := by
      rcases recoh_cyclic_fibre_orbit_separator q (recohCanonicalPrimaryData q 3) S hS with
        hall | ⟨j, hj⟩
      · exact (ho ((recoh_one_orbit_check_iff reps hnonempty).mpr
          (fun B hB C hC => hall B (hfibre B hB) C (hfibre C hC)))).elim
      · exact ⟨j, (recoh_ternary_orbit_check_iff q reps hnonempty j).mpr
          (fun B hB C hC => hj B (hfibre B hB) C (hfibre C hC))⟩
    obtain ⟨i, hi⟩ := recoh_first_passing_exists (recohTernaryOrbitCheck q reps)
      (Finset.univ.sort (· ≤ ·)) ⟨j, by simp, hj⟩
    have hchoice : recohSquareTernaryChoice q entries = some i := by
      change (if recohOneOrbitCheck reps then none else
        recohFirstPassing (recohTernaryOrbitCheck q reps) (Finset.univ.sort (· ≤ ·))) = some i
      rw [if_neg ho]
      exact hi
    exact Or.inr ⟨i, hchoice, recoh_first_passing_sound _ _ i hi⟩





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
      Or
        (@Eq.{1} Bool
          (@Couret.STROBO2TORS.recohOneOrbitCheck.{0} ((i : Fin d) → ZMod (q i))
            (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
              @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            (@Couret.STROBO2TORS.recohCyclicSquareRepresentatives d q entries))
          Bool.true)
        (@Exists.{1}
          (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          fun j =>
          And
            (@Eq.{1}
              (Option.{0}
                (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              (@Couret.STROBO2TORS.recohSquareTernaryChoice d q inst entries)
              (@Option.some.{0}
                (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                j))
            (@Eq.{1} Bool
              (@Couret.STROBO2TORS.recohTernaryOrbitCheck d q inst
                (@Couret.STROBO2TORS.recohCyclicSquareRepresentatives d q entries) j)
              Bool.true)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_square_ternary_choice_complete

