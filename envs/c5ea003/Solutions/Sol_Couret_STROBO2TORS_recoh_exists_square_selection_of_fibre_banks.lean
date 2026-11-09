-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_exists_square_selection_of_fibre_banks
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:54:10.832202+00:00
-- url     : https://prove2.me/submissions/b8f3caa4-f343-4ba7-9c61-20dca67fa02a

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





















/-- Fibrewise existence yields one selection rule depending only on the
observed square, not on the unknown support. This is a classical existence
result, not an executable selection algorithm. -/
theorem p2m_local_recoh_exists_square_selection_of_fibre_banks (k : ℕ)
    (hbank : ∀ S : Finset G, S.card = 3 → ∃ bank : Fin k → AddChar G ℂ,
      Set.InjOn (fun T : Finset G => fun i => recohSupportProbe (bank i) T)
        (squareFibre S)) :
    ∃ select : (G → ℕ) → (Fin k → AddChar G ℂ),
      Function.Injective (fun S : {S : Finset G // S.card = 3} =>
        recohSquareSelectedObservation select S.1) := by
  classical
  have hR : ∀ R : G → ℕ, ∃ bank : Fin k → AddChar G ℂ,
      ∀ S T : Finset G, S.card = 3 → T.card = 3 →
        orderedSquare S = R → orderedSquare T = R →
        (fun i => recohSupportProbe (bank i) S) =
          (fun i => recohSupportProbe (bank i) T) → S = T := by
    intro R
    by_cases hreal : ∃ S : Finset G, S.card = 3 ∧ orderedSquare S = R
    · obtain ⟨U, hU, hUR⟩ := hreal
      obtain ⟨bank, hsep⟩ := hbank U hU
      refine ⟨bank, ?_⟩
      intro S T hS hT hSR hTR heq
      apply hsep ((mem_squareFibre U S).mpr ⟨hS, ?_⟩)
        ((mem_squareFibre U T).mpr ⟨hT, ?_⟩) heq
      · intro z
        exact congrFun (hUR.trans hSR.symm) z
      · intro z
        exact congrFun (hUR.trans hTR.symm) z
    · refine ⟨fun _ => 1, ?_⟩
      intro S T hS _ hSR _ _
      exact (hreal ⟨S, hS, hSR⟩).elim
  let select : (G → ℕ) → (Fin k → AddChar G ℂ) :=
    fun R => Classical.choose (hR R)
  refine ⟨select, ?_⟩
  intro S T heq
  apply Subtype.ext
  have hsquare : orderedSquare S.1 = orderedSquare T.1 := congrArg Prod.fst heq
  have hprobe := congrArg Prod.snd heq
  apply (Classical.choose_spec (hR (orderedSquare S.1))) S.1 T.1 S.2 T.2
    rfl hsquare.symm
  change (fun i => recohSupportProbe (select (orderedSquare S.1) i) S.1) =
    (fun i => recohSupportProbe (select (orderedSquare T.1) i) T.1) at hprobe
  change (fun i => recohSupportProbe (select (orderedSquare S.1) i) S.1) =
    (fun i => recohSupportProbe (select (orderedSquare S.1) i) T.1)
  rw [← hsquare] at hprobe
  exact hprobe













end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (k : Nat),
  (∀ (S : Finset.{p2m_u_0} G),
      @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        @Exists.{p2m_u_0 + 1}
          (Fin k →
            @AddChar.{p2m_u_0, 0} G
              (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
              Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
          fun bank =>
          @Set.InjOn.{p2m_u_0, 0} (Finset.{p2m_u_0} G) (Fin k → Complex)
            (fun T i => @Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i) T)
            (@SetLike.coe.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
              (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G))
              (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S))) →
    @Exists.{p2m_u_0 + 1}
      ((G → Nat) →
        Fin k →
          @AddChar.{p2m_u_0, 0} G
            (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
            Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
      fun select =>
      @Function.Injective.{p2m_u_0 + 1, p2m_u_0 + 1}
        (@Subtype.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun S =>
          @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (Prod.{p2m_u_0, 0} (G → Nat) (Fin k → Complex)) fun S =>
        @Couret.STROBO2TORS.recohSquareSelectedObservation.{p2m_u_0} G inst inst_1 k select
          (@Subtype.val.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
            (fun S =>
              @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_exists_square_selection_of_fibre_banks

