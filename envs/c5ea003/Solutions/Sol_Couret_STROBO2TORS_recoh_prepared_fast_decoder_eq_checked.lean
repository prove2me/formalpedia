-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_prepared_fast_decoder_eq_checked
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:27:37.991742+00:00
-- url     : https://prove2.me/submissions/b29c1545-ca8e-4ae4-93d5-8f7962bd63c1

import Aesop
import Definitions.Def_Couret_RecohPreparedDecoder_2b97e051dec5
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
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCoefficientDecoder_a5265698d3d8

set_option autoImplicit false

/-!
Move the square test before sign recovery, as in Python `_prepare_square`.

The generic prepared decoder filters the chosen representatives before
recovery and retains the complete final checker after recovery.  The two
orders give the same answer whenever a final acceptance implies acceptance
of the representative by the precheck.  For the square test, this implication
follows from invariance under every two-torsion translation, for all finite
supports.  The resulting coefficient backend is therefore equal to the
previously certified backend, under the same support-coverage contract.

This module certifies an order of mathematical operations.  It does not
certify the separate Python cache, parser, or runtime.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]







/-- The early test loses no accepted support if every final acceptance
already implies that the associated representative passes the early test. -/
theorem p2m_local_recoh_prepared_fast_decoder_eq_checked
    (U : Finset G) (half : G → Option G) (recover : Finset G → Finset G)
    (precheck check : Finset G → Bool)
    (hpre : ∀ B, check (recover B) = true → precheck B = true) :
    recohPreparedFastDecoder U half recover precheck check =
      recohCheckedFastDecoder U half recover check := by
  ext S
  simp only [recohPreparedFastDecoder, recohPreparedFastCandidates,
    recohPreparedEdgeSets, recohCheckedFastDecoder, recohFastCandidates,
    Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨E, ⟨hE, _⟩, hrec⟩, hcheck⟩
    exact ⟨⟨E, hE, hrec⟩, hcheck⟩
  · rintro ⟨⟨E, hE, hrec⟩, hcheck⟩
    refine ⟨⟨E, ⟨hE, hpre _ ?_⟩, hrec⟩, hcheck⟩
    rwa [hrec]











variable {J : Type*}

local notation "H₂" => recohTorsionSubgroup (G := G) 2





variable {I : Type*} [Fintype I]







end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (U : Finset.{p2m_u_0} G)
  (half : G → Option.{p2m_u_0} G) (recover : Finset.{p2m_u_0} G → Finset.{p2m_u_0} G)
  (precheck check : Finset.{p2m_u_0} G → Bool),
  (∀ (B : Finset.{p2m_u_0} G), @Eq.{1} Bool (check (recover B)) Bool.true → @Eq.{1} Bool (precheck B) Bool.true) →
    @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Couret.STROBO2TORS.recohPreparedFastDecoder.{p2m_u_0} G inst inst_1 U half recover precheck check)
      (@Couret.STROBO2TORS.recohCheckedFastDecoder.{p2m_u_0} G inst inst_1 U half recover check) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_prepared_fast_decoder_eq_checked

