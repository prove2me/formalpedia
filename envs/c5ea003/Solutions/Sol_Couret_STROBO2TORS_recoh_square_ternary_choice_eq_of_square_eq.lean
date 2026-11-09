-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_square_ternary_choice_eq_of_square_eq
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:03.076208+00:00
-- url     : https://prove2.me/submissions/b6dc881a-5e69-454b-8900-caa923276e3e

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





























/-- Selection depends on the square function alone, even if the typed list
is reordered, split into duplicate entries, or padded by zero entries. -/
theorem p2m_local_recoh_square_ternary_choice_eq_of_square_eq
    (entries other : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (hR : recohTypedSquareValue entries = recohTypedSquareValue other) :
    recohSquareTernaryChoice q entries = recohSquareTernaryChoice q other := by
  have hU : recohSelectedSquareSupport q entries = recohSelectedSquareSupport q other := by
    ext z
    rw [recoh_mem_selected_square_support, recoh_mem_selected_square_support, hR]
  simp only [recohSquareTernaryChoice, recohCyclicSquareRepresentatives, hU, hR]







end Cyclic

end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries other : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat)),
  @Eq.{1} (((i : Fin d) → ZMod (q i)) → Nat)
      (@Couret.STROBO2TORS.recohTypedSquareValue.{0} ((i : Fin d) → ZMod (q i))
        (fun a b =>
          @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
            (Fin.fintype d) a b)
        entries)
      (@Couret.STROBO2TORS.recohTypedSquareValue.{0} ((i : Fin d) → ZMod (q i))
        (fun a b =>
          @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
            (Fin.fintype d) a b)
        other) →
    @Eq.{1}
      (Option.{0}
        (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@Couret.STROBO2TORS.recohSquareTernaryChoice d q inst entries)
      (@Couret.STROBO2TORS.recohSquareTernaryChoice d q inst other) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_square_ternary_choice_eq_of_square_eq

