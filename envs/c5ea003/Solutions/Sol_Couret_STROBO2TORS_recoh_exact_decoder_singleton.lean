-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_exact_decoder_singleton
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:42:39.365778+00:00
-- url     : https://prove2.me/submissions/4f84e916-e2c5-421c-b0d8-920a79101a4f

import Aesop
import Definitions.Def_Couret_RecohCandidateDecoder_966deca9afb6
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_mem_exact_decoder_iff
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883

set_option autoImplicit false

/-!
Structured candidates for exact RECOH reconstruction.

For a genuine triple S = {a,b,c}, its three distinct off-diagonal sums
E = {a+b,a+c,b+c} belong to the support of the ordered square.  With
sigma = a+b+c, they satisfy sum E = sigma+sigma and S = sigma-E.
This supplies a complete candidate generator using only the input square.

The finite candidate generator uses decidable group operations.  The exact
complex-character filter below is explicitly noncomputable: this module
certifies its mathematical result, not an executable representation of
complex numbers or a refinement of a separate Python implementation.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]







variable [Fintype G]





















/-- A reconstructing bank leaves precisely the actual support in the exact
decoder.  The bank hypothesis is discharged by the optimal-bank theorem. -/
theorem p2m_local_recoh_exact_decoder_singleton {I : Type*}
    (bank : I → AddChar G ℂ)
    (hinj : Function.Injective (fun S : {S : Finset G // S.card = 3} =>
      recohObservation bank S.1))
    (S : Finset G) (hS : S.card = 3) :
    recohExactDecoder bank (recohObservation bank S) = {S} := by
  classical
  ext T
  rw [recoh_mem_exact_decoder_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hT, hobs⟩
    exact congrArg Subtype.val (hinj (show
      recohObservation bank (⟨T, hT⟩ : {T : Finset G // T.card = 3}).1 =
        recohObservation bank (⟨S, hS⟩ : {S : Finset G // S.card = 3}).1 from hobs))
  · rintro rfl
    exact ⟨hS, rfl⟩



end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] {I : Type p2m_u_1}
  (bank :
    I →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)),
  (@Function.Injective.{p2m_u_0 + 1, max (p2m_u_1 + 1) (p2m_u_0 + 1)}
      (@Subtype.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun S =>
        @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (Prod.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex)) fun S =>
      @Couret.STROBO2TORS.recohObservation.{p2m_u_0, p2m_u_1} G inst inst_1 I bank
        (@Subtype.val.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
          (fun S =>
            @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          S)) →
    ∀ (S : Finset.{p2m_u_0} G),
      @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@Couret.STROBO2TORS.recohExactDecoder.{p2m_u_0, p2m_u_1} G inst inst_1 inst_2 I bank
            (@Couret.STROBO2TORS.recohObservation.{p2m_u_0, p2m_u_1} G inst inst_1 I bank S))
          (@Singleton.singleton.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@Finset.instSingleton.{p2m_u_0} (Finset.{p2m_u_0} G)) S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_exact_decoder_singleton

