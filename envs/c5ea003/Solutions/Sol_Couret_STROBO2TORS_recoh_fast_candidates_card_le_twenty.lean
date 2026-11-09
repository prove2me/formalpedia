-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_fast_candidates_card_le_twenty
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:26:46.868286+00:00
-- url     : https://prove2.me/submissions/c2afb423-8902-4257-afe1-a469c61497ee

import Aesop
import Definitions.Def_Couret_RecohFastDecoder_5bb89f11acce
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
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohDecoderBounds_60ec29457baa
import Definitions.Def_Couret_RecohCyclicHalves_383c4510168a
import Definitions.Def_Couret_RecohSignRecovery_71a8a4a1ce8a

set_option autoImplicit false

/-!
One-representative RECOH decoder on an explicitly supplied finite support.

The construction visits only the three-element subsets of U.  A supplied
doubling solver chooses one half-sum for each feasible edge set, and a
translation-recovery function turns the corresponding representative into
one candidate.  The final filter uses the complete labelled observation.
No enumeration of the ambient group or its two-torsion subgroup occurs in
these definitions.  Their construction needs no Fintype instance on G.

The refinement theorem proves equality with recohExactDecoder, provided U
covers the observed square support and the half-sum and recovery contracts
hold.  Sign recovery supplies the recovery contract for binary coordinates
inside any larger labelled character bank.  Complex equality remains
noncomputable here: this is a Lean refinement of the mathematical decoder,
not a verification of the external Python parser or arithmetic runtime.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























omit [AddCommGroup G] [DecidableEq G] in
/-- The twenty-set bound depends only on the supplied sparse support. -/
theorem recoh_sparse_edge_sets_card_le_twenty (U : Finset G) (hU : U.card ≤ 6) :
    (U.powersetCard 3).card ≤ 20 := by
  rw [Finset.card_powersetCard]
  calc
    U.card.choose 3 ≤ Nat.choose 6 3 := Nat.choose_le_choose 3 hU
    _ = 20 := by decide



theorem recoh_fast_candidates_card_le
    (U : Finset G) (half : G → Option G) (recover : Finset G → Finset G) :
    (recohFastCandidates U half recover).card ≤ (U.powersetCard 3).card := by
  exact Finset.card_image_le.trans (Finset.card_filter_le _ _)

/-- The number of recovered candidates is at most twenty, independently
of the cardinality of the ambient group and of its two-torsion subgroup. -/
theorem p2m_local_recoh_fast_candidates_card_le_twenty
    (U : Finset G) (half : G → Option G) (recover : Finset G → Finset G)
    (hU : U.card ≤ 6) : (recohFastCandidates U half recover).card ≤ 20 := by
  exact (recoh_fast_candidates_card_le U half recover).trans
    (recoh_sparse_edge_sets_card_le_twenty U hU)







section FiniteRefinement

variable [Fintype G]









end FiniteRefinement

variable {r : ℕ}

local notation "H₂" => recohTorsionSubgroup (G := G) 2











end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (U : Finset.{p2m_u_0} G)
  (half : G → Option.{p2m_u_0} G) (recover : Finset.{p2m_u_0} G → Finset.{p2m_u_0} G),
  @LE.le.{0} Nat instLENat (@Finset.card.{p2m_u_0} G U) (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) →
    @LE.le.{0} Nat instLENat
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Couret.STROBO2TORS.recohFastCandidates.{p2m_u_0} G inst inst_1 U half recover))
      (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_fast_candidates_card_le_twenty

