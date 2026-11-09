-- Prove2me | Definitions.Def_Couret_RecohCandidateDecoder_966deca9afb6
-- name    : Couret_RecohCandidateDecoder_966deca9afb6
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:02:19.301965+00:00
-- url     : https://prove2.me/theorems/544f14ea-b580-4650-9491-a8ffc8ddf62c
-- title:
--   Candidates from pair-sum edges
-- statement:
--   The edge decoder reconstructs support candidates from a finite set of pair-sum positions and a total-sum parameter. The square-support, candidate-pair and candidate-support constructions enumerate possibilities for a supplied ordered-square function. The exact decoder filters all three-element supports against the complete observation. These definitions separate coarse candidate generation from semantic verification.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCandidateDecoder.lean; source file SHA-256 776f7f56ee0e11b95b74a89da277d67a6f783658f9375affe48c6fa12273ef52

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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
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

/-- Reflect the three proposed edge sums about their proposed total. -/
def recohEdgeDecode (E : Finset G) (sigma : G) : Finset G :=
  E.image (fun e => sigma - e)

theorem recoh_edge_decode_card (E : Finset G) (sigma : G) :
    (recohEdgeDecode E sigma).card = E.card := by
  apply Finset.card_image_of_injective
  intro x y h
  exact sub_right_injective h

/-- Every sum of two support elements has a positive square coefficient. -/
theorem recoh_ordered_square_pos_of_mem (S : Finset G) (a b : G)
    (ha : a ∈ S) (hb : b ∈ S) : 0 < orderedSquare S (a + b) := by
  unfold orderedSquare
  apply Finset.sum_pos_iff.mpr
  refine ⟨a, ha, ?_⟩
  apply Finset.sum_pos_iff.mpr
  exact ⟨b, hb, by simp⟩

variable [Fintype G]

/-- The known labelled support of an input square. -/
def recohSquareSupport (R : G → ℕ) : Finset G :=
  Finset.univ.filter (fun z => 0 < R z)

omit [AddCommGroup G] [DecidableEq G] in
@[simp] theorem recoh_mem_square_support (R : G → ℕ) (z : G) :
    z ∈ recohSquareSupport R ↔ 0 < R z := by
  simp [recohSquareSupport]



/-- Enumerate edge triples together with all solutions of their doubling
equation.  Both the finite enumeration and its test are decidable. -/
def recohCandidatePairs (R : G → ℕ) : Finset (Finset G × G) :=
  (((recohSquareSupport R).powersetCard 3) ×ˢ Finset.univ).filter
    (fun p => p.2 + p.2 = p.1.sum id)

/-- Proposed support triples, prior to checking the complete observation. -/
def recohCandidates (R : G → ℕ) : Finset (Finset G) :=
  (recohCandidatePairs R).image (fun p => recohEdgeDecode p.1 p.2)

theorem recoh_mem_candidates_iff (R : G → ℕ) (S : Finset G) :
    S ∈ recohCandidates R ↔
      ∃ E : Finset G, ∃ sigma : G,
        E ⊆ recohSquareSupport R ∧ E.card = 3 ∧
        sigma + sigma = E.sum id ∧ recohEdgeDecode E sigma = S := by
  simp only [recohCandidates, recohCandidatePairs, Finset.mem_image,
    Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard,
    Finset.mem_univ, and_true, Prod.exists]
  constructor
  · rintro ⟨E, sigma, ⟨⟨hsub, hcard⟩, hsum⟩, hS⟩
    exact ⟨E, sigma, hsub, hcard, hsum, hS⟩
  · rintro ⟨E, sigma, hsub, hcard, hsum, hS⟩
    exact ⟨E, sigma, ⟨⟨hsub, hcard⟩, hsum⟩, hS⟩



/-- Completeness: the true support occurs in the finite candidate generator. -/
theorem recoh_candidates_complete (S : Finset G) (hS : S.card = 3) :
    S ∈ recohCandidates (orderedSquare S) := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS
  have he12 : a + b ≠ a + c := fun h => hbc (add_left_cancel h)
  have he13 : a + b ≠ b + c := by
    intro h
    apply hac
    have h' : a + b = c + b := by simpa only [add_comm b c] using h
    exact add_right_cancel h'
  have he23 : a + c ≠ b + c := fun h => hab (add_right_cancel h)
  apply (recoh_mem_candidates_iff _ _).mpr
  refine ⟨{a + b, a + c, b + c}, a + b + c, ?_, ?_, ?_, ?_⟩
  · intro e he
    rw [recoh_mem_square_support]
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact recoh_ordered_square_pos_of_mem _ a b (by simp) (by simp)
    · exact recoh_ordered_square_pos_of_mem _ a c (by simp) (by simp)
    · exact recoh_ordered_square_pos_of_mem _ b c (by simp) (by simp)
  · simp [he12, he13, he23]
  · simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      not_or, he12, he13, he23, not_false_eq_true, and_self,
      Finset.sum_singleton, id_eq]
    abel
  · have ha : (a + b + c) - (a + b) = c := by abel
    have hb : (a + b + c) - (a + c) = b := by abel
    have hc : (a + b + c) - (b + c) = a := by abel
    ext x
    simp only [recohEdgeDecode, Finset.image_insert, Finset.image_singleton,
      ha, hb, hc, Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- Exact observation filtering.  Deciding equality in C is not claimed to
be an executable operation; an exact cyclotomic implementation is separate. -/
noncomputable def recohExactDecoder {I : Type*}
    (bank : I → AddChar G ℂ) (obs : (G → ℕ) × (I → ℂ)) : Finset (Finset G) := by
  classical
  exact (recohCandidates obs.1).filter (fun S => recohObservation bank S = obs)







end Couret.STROBO2TORS


