-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_square_injective_of_trivial_two_torsion
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:17:19.250897+00:00
-- url     : https://prove2.me/submissions/706504e8-ca97-4df9-9731-002a6f16c20d

import Aesop
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a

set_option autoImplicit false

/-!
The optimal size of a fixed bank of individual, labelled complex
Fourier coefficients, given the labelled ordered convolution square of a
three-element support.  Zero is allowed in the support.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



/-- With trivial two-torsion, the square itself reconstructs every triple. -/
theorem p2m_local_recoh_square_injective_of_trivial_two_torsion
    (h2 : ∀ u : G, u + u = 0 → u = 0) :
    Function.Injective (fun S : {S : Finset G // S.card = 3} => orderedSquare S.1) := by
  intro S T h
  apply Subtype.ext
  rcases orderedSquare_classification_necessary S.1 T.1 S.2 T.2 (congrFun h) with ho | he
  · obtain ⟨u, hu, ht⟩ := ho
    have hu0 := h2 u hu
    simpa [hu0, translateSupport] using ht.symm
  · obtain ⟨a, b, d, u, hd, hd0, _⟩ := he
    exact (hd0 (h2 d hd)).elim

variable [Fintype G]









end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G],
  (∀ (u : G),
      @Eq.{p2m_u_0 + 1} G
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            u u)
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
        @Eq.{p2m_u_0 + 1} G u
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))) →
    @Function.Injective.{p2m_u_0 + 1, p2m_u_0 + 1}
      (@Subtype.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun S =>
        @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (G → Nat) fun S =>
      @Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
        (@Subtype.val.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
          (fun S =>
            @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_square_injective_of_trivial_two_torsion

