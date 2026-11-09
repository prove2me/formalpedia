-- Prove2me | Definitions.Def_Couret_RecohFastDecoder_5bb89f11acce
-- name    : Couret_RecohFastDecoder_5bb89f11acce
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:03:22.230007+00:00
-- url     : https://prove2.me/theorems/e315baf5-ad05-41f2-b9fc-f04576038f8a
-- title:
--   Fast edge candidates and checked support decoding
-- statement:
--   Given $U\subseteq G$ and a partial half solver, feasible edge sets are three-subsets $E\subseteq U$ whose total has a returned half $\sigma$. Their representative support is $\{\sigma-e:e\in E\}$. The fast candidate family maps these representatives through a recovery function.
--
--   The bundle defines semantic-observation and Boolean-check filters, the exact translation-recovery contract, and sign-based support recovery. The contract requires triple-cardinality preservation and exact recovery of any two-torsion translate compatible with the supplied observation.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohFastDecoder.lean; source file SHA-256 d84bc4908e0c9ab4ae54de4f0901e08828a787fa98a3987c63969ea57c85e8da

import Aesop
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

/-- Only edge sets whose total has a half-sum are retained. -/
def recohFeasibleEdgeSets (U : Finset G) (half : G → Option G) : Finset (Finset G) :=
  (U.powersetCard 3).filter (fun E => (half (E.sum id)).isSome)

/-- One representative for an edge set.  The default is ignored by the
decoder because infeasible edge sets have already been removed. -/
def recohEdgeRepresentative (half : G → Option G) (E : Finset G) : Finset G :=
  recohEdgeDecode E ((half (E.sum id)).getD 0)

/-- One recovered support per feasible edge set, with duplicate supports
identified by the finite-set image. -/
def recohFastCandidates (U : Finset G) (half : G → Option G)
    (recover : Finset G → Finset G) : Finset (Finset G) :=
  (recohFeasibleEdgeSets U half).image
    (fun E => recover (recohEdgeRepresentative half E))

/-- Complete observation filtering after the one-representative construction. -/
noncomputable def recohFastDecoder {I : Type*}
    (U : Finset G) (half : G → Option G) (recover : Finset G → Finset G)
    (bank : I → AddChar G ℂ) (obs : (G → ℕ) × (I → ℂ)) : Finset (Finset G) := by
  classical
  exact (recohFastCandidates U half recover).filter
    (fun S => recohObservation bank S = obs)

/-- Executable filtering interface: an exact arithmetic backend supplies
the Boolean checker, independently of the mathematical complex filter. -/
def recohCheckedFastDecoder
    (U : Finset G) (half : G → Option G) (recover : Finset G → Finset G)
    (check : Finset G → Bool) : Finset (Finset G) :=
  (recohFastCandidates U half recover).filter (fun S => check S = true)

/-- Recovery preserves triple cardinality and reconstructs every
two-torsion translate compatible with the target observation. -/
def RecohTranslationRecoverySpec {I : Type*}
    (bank : I → AddChar G ℂ) (obs : (G → ℕ) × (I → ℂ))
    (recover : Finset G → Finset G) : Prop :=
  (∀ B : Finset G, B.card = 3 → (recover B).card = 3) ∧
  (∀ B : Finset G, B.card = 3 → ∀ u : G, u + u = 0 →
    recohObservation bank (translateSupport B u) = obs →
      recover B = translateSupport B u)

omit [DecidableEq G] in
@[simp]
theorem recoh_mem_feasible_edge_sets (U E : Finset G) (half : G → Option G) :
    E ∈ recohFeasibleEdgeSets U half ↔
      E ⊆ U ∧ E.card = 3 ∧ (half (E.sum id)).isSome := by
  simp [recohFeasibleEdgeSets, and_assoc]

theorem recoh_edge_representative_card (half : G → Option G) (E : Finset G) :
    (recohEdgeRepresentative half E).card = E.card :=
  recoh_edge_decode_card E _

/-- Changing the chosen half-sum translates the reflected edge set by
the difference of the two half-sums.  The identity holds for every edge set. -/
theorem recoh_edge_decode_change_half (E : Finset G) (sigma sigma0 : G) :
    recohEdgeDecode E sigma =
      translateSupport (recohEdgeDecode E sigma0) (sigma - sigma0) := by
  unfold recohEdgeDecode translateSupport
  rw [Finset.image_image]
  apply Finset.image_congr
  intro e _
  change sigma - e = (sigma0 - e) + (sigma - sigma0)
  abel



















section FiniteRefinement

variable [Fintype G]









end FiniteRefinement

variable {r : ℕ}

local notation "H₂" => recohTorsionSubgroup (G := G) 2

/-- Recover a support by comparing binary readings and translating by
the explicitly recovered two-torsion coordinate vector. -/
noncomputable def recohSignRecoverSupport
    (bank : Fin r → AddChar G ℂ) (e : H₂ ≃+ (Fin r → ZMod 2))
    (obs : Fin r → ℂ) (B : Finset G) : Finset G :=
  translateSupport B
    (recohRecoverTranslation e (fun i => recohSupportProbe (bank i) B) obs : G)









end Couret.STROBO2TORS


