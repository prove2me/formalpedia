-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_prepared_fast_candidates_card_le_twenty
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:27:07.446853+00:00
-- url     : https://prove2.me/submissions/8e8c58f0-e2c9-4fbe-a7ef-242e438848e9

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_prepared_edge_sets_card_le_twenty
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











theorem p2m_local_recoh_prepared_fast_candidates_card_le_twenty
    (U : Finset G) (half : G → Option G) (recover : Finset G → Finset G)
    (precheck : Finset G → Bool) (hU : U.card ≤ 6) :
    (recohPreparedFastCandidates U half recover precheck).card ≤ 20 := by
  exact Finset.card_image_le.trans
    (recoh_prepared_edge_sets_card_le_twenty U half precheck hU)







variable {J : Type*}

local notation "H₂" => recohTorsionSubgroup (G := G) 2





variable {I : Type*} [Fintype I]







end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (U : Finset.{p2m_u_0} G)
  (half : G → Option.{p2m_u_0} G) (recover : Finset.{p2m_u_0} G → Finset.{p2m_u_0} G)
  (precheck : Finset.{p2m_u_0} G → Bool),
  @LE.le.{0} Nat instLENat (@Finset.card.{p2m_u_0} G U) (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) →
    @LE.le.{0} Nat instLENat
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Couret.STROBO2TORS.recohPreparedFastCandidates.{p2m_u_0} G inst inst_1 U half recover precheck))
      (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_prepared_fast_candidates_card_le_twenty

