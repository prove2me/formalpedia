-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_square_selection_injective_on_fibre
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:42:55.816983+00:00
-- url     : https://prove2.me/submissions/5067a7e6-2a1b-43be-a00d-84b742a5f01e

import Aesop
import Definitions.Def_Couret_RecohFibreOptimal_b9d6825ce497
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
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
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Mathlib.Data.Nat.Log

set_option autoImplicit false

/-!
Optimal character banks selected from the observed labelled ordered square.
The selected bank is fixed on its entire fibre. Selection is existential;
this module does not implement selection from raw or typed decoder input.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]























/-- Any reconstructing square-selection rule restricts to an ordinary fixed
bank on each full fibre, so the information lower bounds still apply. -/
theorem p2m_local_recoh_square_selection_injective_on_fibre {k : ℕ}
    (select : (G → ℕ) → (Fin k → AddChar G ℂ))
    (hinj : Function.Injective (fun S : {S : Finset G // S.card = 3} =>
      recohSquareSelectedObservation select S.1)) (S : Finset G) :
    Set.InjOn (fun T : Finset G => fun i =>
      recohSupportProbe (select (orderedSquare S) i) T) (squareFibre S) := by
  intro T hT U hU heq
  obtain ⟨hT3, hsT⟩ := (mem_squareFibre S T).mp hT
  obtain ⟨hU3, hsU⟩ := (mem_squareFibre S U).mp hU
  have hST : orderedSquare S = orderedSquare T := funext hsT
  have hSU : orderedSquare S = orderedSquare U := funext hsU
  have hobs : recohSquareSelectedObservation select T =
      recohSquareSelectedObservation select U := by
    apply Prod.ext
    · exact hST.symm.trans hSU
    · change (fun i => recohSupportProbe (select (orderedSquare T) i) T) =
        (fun i => recohSupportProbe (select (orderedSquare U) i) U)
      simpa only [← hST, ← hSU] using heq
  exact congrArg Subtype.val (hinj (a₁ := ⟨T, hT3⟩) (a₂ := ⟨U, hU3⟩) hobs)











end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] {k : Nat}
  (select :
    (G → Nat) →
      Fin k →
        @AddChar.{p2m_u_0, 0} G
          (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
          Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)),
  (@Function.Injective.{p2m_u_0 + 1, p2m_u_0 + 1}
      (@Subtype.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun S =>
        @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (Prod.{p2m_u_0, 0} (G → Nat) (Fin k → Complex)) fun S =>
      @Couret.STROBO2TORS.recohSquareSelectedObservation.{p2m_u_0} G inst inst_1 k select
        (@Subtype.val.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
          (fun S =>
            @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          S)) →
    ∀ (S : Finset.{p2m_u_0} G),
      @Set.InjOn.{p2m_u_0, 0} (Finset.{p2m_u_0} G) (Fin k → Complex)
        (fun T i =>
          @Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst
            (select (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 S) i) T)
        (@SetLike.coe.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
          (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_square_selection_injective_on_fibre

