-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_fibre_card_le_two_pow_of_separating_bank
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:03:04.248262+00:00
-- url     : https://prove2.me/submissions/1f8f14f8-6045-43f9-872d-6226b919c9d6

import Aesop
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_eq_or_neg_of_square_eq
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

/-!
Information lower bound for a bank chosen after the labelled ordered
square is known.  Reconstructing means actual injectivity on the existing
finite square fibre.  The result applies to arbitrary complex characters,
including probes which vanish on that fibre.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



/-- `k` fixed character slots distinguish at most `2^k` members of any
square fibre.  The bank may depend on this fibre, but not on the unknown
member within it.  This theorem does not assert an adaptive-tree bound. -/
theorem p2m_local_recoh_fibre_card_le_two_pow_of_separating_bank
    (S : Finset G) {k : ℕ} (bank : Fin k → AddChar G ℂ)
    (hsep : Set.InjOn
      (fun T : Finset G => fun i => recohSupportProbe (bank i) T)
      (squareFibre S)) :
    (squareFibre S).card ≤ 2 ^ k := by
  classical
  let bits : {T : Finset G // T ∈ squareFibre S} → (Fin k → Bool) :=
    fun T i => decide (recohSupportProbe (bank i) T.1 = recohSupportProbe (bank i) S)
  have hbits : Function.Injective bits := by
    intro A B hAB
    apply Subtype.ext
    apply hsep A.2 B.2
    funext i
    have hi := congrFun hAB i
    have hA := recoh_support_probe_eq_or_neg_of_square_eq (bank i) A.1 S
      (fun z => (((mem_squareFibre S A.1).mp A.2).2 z).symm)
    have hB := recoh_support_probe_eq_or_neg_of_square_eq (bank i) B.1 S
      (fun z => (((mem_squareFibre S B.1).mp B.2).2 z).symm)
    by_cases ha : recohSupportProbe (bank i) A.1 = recohSupportProbe (bank i) S
    · have hb : recohSupportProbe (bank i) B.1 = recohSupportProbe (bank i) S := by
        simpa [bits, ha] using hi.symm
      exact ha.trans hb.symm
    · have hb : recohSupportProbe (bank i) B.1 ≠ recohSupportProbe (bank i) S := by
        intro hb
        have hfalse : false = true := by simpa [bits, ha, hb] using hi
        cases hfalse
      exact (hA.resolve_left ha).trans (hB.resolve_left hb).symm
  have hcard := Fintype.card_le_of_injective bits hbits
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] using hcard





end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G) {k : Nat}
  (bank :
    Fin k →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)),
  @Set.InjOn.{p2m_u_0, 0} (Finset.{p2m_u_0} G) (Fin k → Complex)
      (fun T i => @Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i) T)
      (@SetLike.coe.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
        (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S)) →
    @LE.le.{0} Nat instLENat
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_fibre_card_le_two_pow_of_separating_bank

