-- Prove2me | Definitions.Def_Couret_RecohSquareSelector_3b7a2954c02a
-- name    : Couret_RecohSquareSelector_3b7a2954c02a
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:10:11.499238+00:00
-- url     : https://prove2.me/theorems/4ffde924-24ce-43e8-b555-75fa6e8c109c
-- title:
--   Selecting a ternary orbit separator from square data
-- statement:
--   This bundle defines checks for two-torsion partnership, a representative family obtained from square-compatible edge sets, a one-orbit check, and a check that a proposed reading separates distinct orbits. A first-passing search returns the earliest successful test entry.
--
--   For cyclic products it keeps the positive square support, constructs representatives, compares reduced three-primary readings and selects no ternary coordinate for a single-orbit family, otherwise the first coordinate passing the orbit-separation check. This is the finite selection interface behind the square-dependent bank.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohSquareSelector.lean; source file SHA-256 a8eaaafaf12bee0781361925c6726f9d658ee4df71e8e3c8436c68366ccc7438

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCyclicPreparedDecoder_0ae8cdf0a932
import Definitions.Def_Couret_RecohTernaryFibreSelector_4c0db0f29983

set_option autoImplicit false

/-!
Selection from the labelled ordered square using at most twenty explicit
representatives. All runtime checks use finite supports, cyclic coordinates
and integer cyclotomic coefficients. No ambient-group search occurs.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Decide two-torsion translation using differences of points already in
the two supports. For triples there are at most nine such differences. -/
def recohTorsionOrbitCheck (B C : Finset G) : Bool :=
  decide (∃ x ∈ B, ∃ y ∈ C,
    (y - x) + (y - x) = 0 ∧ C = translateSupport B (y - x))

theorem recoh_torsion_orbit_check_iff (B C : Finset G) (hB : B.Nonempty) :
    recohTorsionOrbitCheck B C = true ↔ OrdinaryPartner B C := by
  simp only [recohTorsionOrbitCheck, decide_eq_true_eq]
  constructor
  · rintro ⟨x, _, y, _, hu, hC⟩
    exact ⟨y - x, hu, hC⟩
  · rintro ⟨u, hu, hC⟩
    obtain ⟨x, hx⟩ := hB
    have hxu : x + u ∈ C := by
      rw [hC]
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    refine ⟨x, hx, x + u, hxu, ?_, ?_⟩
    · simpa only [add_sub_cancel_left] using hu
    · simpa only [add_sub_cancel_left] using hC

theorem recoh_ordinary_partner_refl (B : Finset G) : OrdinaryPartner B B := by
  exact ⟨0, by simp, by simp [translateSupport]⟩

theorem recoh_ordinary_partner_symm {B C : Finset G}
    (h : OrdinaryPartner B C) : OrdinaryPartner C B := by
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨u, hu, (translateSupport_twice B u hu).symm⟩

theorem recoh_ordinary_partner_trans {A B C : Finset G}
    (hAB : OrdinaryPartner A B) (hBC : OrdinaryPartner B C) : OrdinaryPartner A C := by
  obtain ⟨u, hu, rfl⟩ := hAB
  obtain ⟨v, hv, hC⟩ := hBC
  refine ⟨u + v, ?_, ?_⟩
  · calc
      (u + v) + (u + v) = (u + u) + (v + v) := by abel
      _ = 0 := by simp [hu, hv]
  · exact hC.trans (translateSupport_add A u v)

/-- Chosen half-sums followed by the exact square check; the resulting
set contains representatives of every compatible two-torsion orbit. -/
def recohSquareRepresentatives (U : Finset G) (R : G → ℕ)
    (half : G → Option G) : Finset (Finset G) :=
  (recohPreparedEdgeSets U half (fun B => recohSparseSquareCheck U B R)).image
    (recohEdgeRepresentative half)

theorem recoh_square_representatives_sound (U : Finset G) (R : G → ℕ)
    (half : G → Option G) (hR : ∀ z, R z ≠ 0 → z ∈ U)
    (B : Finset G) (hB : B ∈ recohSquareRepresentatives U R half) :
    B.card = 3 ∧ orderedSquare B = R := by
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hB
  obtain ⟨hE, hsquare⟩ := Finset.mem_filter.mp hE
  have hcard := ((recoh_mem_feasible_edge_sets U E half).mp hE).2.1
  exact ⟨(recoh_edge_representative_card half E).trans hcard,
    (recoh_sparse_square_check_iff U _ R hR).mp hsquare⟩



/-- Test whether every pair of retained representatives lies in one orbit.
Defined before any ambient finiteness instance, so bounded quantification
is implemented directly over the supplied finite set. -/
def recohOneOrbitCheck (reps : Finset (Finset G)) : Bool :=
  decide (∀ B ∈ reps, ∀ C ∈ reps, recohTorsionOrbitCheck B C = true)

theorem recoh_one_orbit_check_iff (reps : Finset (Finset G))
    (hnonempty : ∀ B ∈ reps, B.Nonempty) :
    recohOneOrbitCheck reps = true ↔
      ∀ B ∈ reps, ∀ C ∈ reps, OrdinaryPartner B C := by
  simp only [recohOneOrbitCheck, decide_eq_true_eq]
  constructor
  · intro h B hB C hC
    exact (recoh_torsion_orbit_check_iff B C (hnonempty B hB)).mp (h B hB C hC)
  · intro h B hB C hC
    exact (recoh_torsion_orbit_check_iff B C (hnonempty B hB)).mpr (h B hB C hC)

/-- A bounded representative-pair test, without an ambient finiteness
instance. The equality backend is supplied as an executable Boolean. -/
def recohOrbitSeparatorCheck (reps : Finset (Finset G))
    (equal : Finset G → Finset G → Bool) : Bool :=
  decide (∀ B ∈ reps, ∀ C ∈ reps,
    recohTorsionOrbitCheck B C = true ∨ ¬ equal B C = true)

variable [Fintype G]

/-- Every triple with the observed square belongs to an orbit represented
by the sparse construction. This proof does not enumerate that orbit. -/
theorem recoh_square_representatives_complete
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (hhalf : RecohHalfSolverSpec half) (hR : ∀ z, R z ≠ 0 → z ∈ U)
    (S : Finset G) (hS : S.card = 3) (hsquare : orderedSquare S = R) :
    ∃ B ∈ recohSquareRepresentatives U R half, OrdinaryPartner B S := by
  obtain ⟨E, sigma, hE, hcard, hsigma, hdecode⟩ :=
    (recoh_mem_candidates_iff (orderedSquare S) S).mp (recoh_candidates_complete S hS)
  obtain ⟨sigma0, hsigma0⟩ := hhalf.2 (E.sum id) ⟨sigma, hsigma⟩
  have hdouble0 : sigma0 + sigma0 = E.sum id := hhalf.1 _ _ hsigma0
  have hu : (sigma - sigma0) + (sigma - sigma0) = 0 :=
    (double_eq_iff_two_torsion sigma0 sigma).mp (hdouble0.trans hsigma.symm)
  have hshift : translateSupport (recohEdgeDecode E sigma0) (sigma - sigma0) = S :=
    (recoh_edge_decode_change_half E sigma sigma0).symm.trans hdecode
  have hrep : recohEdgeRepresentative half E = recohEdgeDecode E sigma0 := by
    simp only [recohEdgeRepresentative, hsigma0, Option.getD_some]
  have hEs : E ⊆ U := by
    intro z hz
    have hp := (recoh_mem_square_support (orderedSquare S) z).mp (hE hz)
    exact hR z (by rw [← hsquare]; exact Nat.ne_of_gt hp)
  have hfeasible : E ∈ recohFeasibleEdgeSets U half :=
    (recoh_mem_feasible_edge_sets U E half).mpr
      ⟨hEs, hcard, by simp only [hsigma0, Option.isSome_some]⟩
  have hsquareB : orderedSquare (recohEdgeRepresentative half E) = R := by
    rw [hrep]
    calc
      orderedSquare (recohEdgeDecode E sigma0) =
          orderedSquare (translateSupport (recohEdgeDecode E sigma0) (sigma - sigma0)) :=
        (recoh_ordered_square_two_torsion_translate _ _ hu).symm
      _ = R := by rw [hshift]; exact hsquare
  refine ⟨recohEdgeRepresentative half E, ?_, sigma - sigma0, hu, ?_⟩
  · apply Finset.mem_image.mpr
    refine ⟨E, Finset.mem_filter.mpr ⟨hfeasible, ?_⟩, rfl⟩
    exact (recoh_sparse_square_check_iff U _ R hR).mpr hsquareB
  · rw [hrep]
    exact hshift.symm

section FiniteSelection

variable {α : Type*}

/-- Retain the first passing index in the supplied finite order. -/
def recohFirstPassing (test : α → Bool) : List α → Option α
  | [] => none
  | a :: rest => if test a then some a else recohFirstPassing test rest





end FiniteSelection

section Cyclic

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

/-- Canonical support of the square function, including on arbitrary typed
inputs: zero-count entries cannot affect selection. -/
def recohSelectedSquareSupport
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    Finset ((i : Fin d) → ZMod (q i)) :=
  (recohTypedSquareSupport entries).filter (fun z => recohTypedSquareValue entries z ≠ 0)

omit [∀ i, NeZero (q i)] in
theorem recoh_mem_selected_square_support
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (z : (i : Fin d) → ZMod (q i)) :
    z ∈ recohSelectedSquareSupport q entries ↔ recohTypedSquareValue entries z ≠ 0 := by
  simp only [recohSelectedSquareSupport, Finset.mem_filter]
  exact and_iff_right_of_imp (recoh_typed_square_covered entries z)

theorem recoh_selected_square_support_covered
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (z : (i : Fin d) → ZMod (q i)) (hz : recohTypedSquareValue entries z ≠ 0) :
    z ∈ recohSelectedSquareSupport q entries :=
  (recoh_mem_selected_square_support q entries z).mpr hz

/-- The square-only representative construction for the cyclic presentation. -/
def recohCyclicSquareRepresentatives
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    Finset (Finset ((i : Fin d) → ZMod (q i))) :=
  recohSquareRepresentatives (recohSelectedSquareSupport q entries)
    (recohTypedSquareValue entries) (recohProductHalf q)

/-- Exact equality of two prospective ternary readings; neither reading
needs to have been measured. -/
def recohTernaryReadingEqual (j : RecohPrimaryCoordinate q 3)
    (B C : Finset ((i : Fin d) → ZMod (q i))) : Bool :=
  recohSparseEqual
    (recohReducedTerms 3 ((recohCanonicalPrimaryData q 3).exponent j)
      (recohCyclicExponents q j.val B))
    (recohReducedTerms 3 ((recohCanonicalPrimaryData q 3).exponent j)
      (recohCyclicExponents q j.val C))

theorem recoh_ternary_reading_equal_iff (j : RecohPrimaryCoordinate q 3)
    (B C : Finset ((i : Fin d) → ZMod (q i))) :
    recohTernaryReadingEqual q j B C = true ↔
      recohSupportProbe (recohCyclicPrimaryBank q 3 (recohCanonicalPrimaryData q 3) j) B =
        recohSupportProbe (recohCyclicPrimaryBank q 3 (recohCanonicalPrimaryData q 3) j) C := by
  let k := (recohCanonicalPrimaryData q 3).exponent j
  let ζ := recohCyclicRoot (3 ^ (k + 1))
  have hζ : IsPrimitiveRoot ζ (3 ^ (k + 1)) := recoh_cyclic_root_primitive _
  rw [recohTernaryReadingEqual,
    recoh_reduced_coefficients_equal_iff Nat.prime_three k hζ _ _
      (recoh_reduced_terms_reduced Nat.prime_three k _)
      (recoh_reduced_terms_reduced Nat.prime_three k _),
    recoh_reduced_terms_value Nat.prime_three k hζ,
    recoh_reduced_terms_value Nat.prime_three k hζ]
  rw [recoh_cyclic_primary_bank_interpret q 3 (recohCanonicalPrimaryData q 3) j B,
    recoh_cyclic_primary_bank_interpret q 3 (recohCanonicalPrimaryData q 3) j C]

/-- A coordinate passes if it distinguishes every pair of distinct orbits
represented in the square-only candidate set. -/
def recohTernaryOrbitCheck
    (reps : Finset (Finset ((i : Fin d) → ZMod (q i))))
    (j : RecohPrimaryCoordinate q 3) : Bool :=
  recohOrbitSeparatorCheck reps (recohTernaryReadingEqual q j)

theorem recoh_ternary_orbit_check_iff
    (reps : Finset (Finset ((i : Fin d) → ZMod (q i))))
    (hnonempty : ∀ B ∈ reps, B.Nonempty) (j : RecohPrimaryCoordinate q 3) :
    recohTernaryOrbitCheck q reps j = true ↔
      ∀ B ∈ reps, ∀ C ∈ reps,
        recohSupportProbe (recohCyclicPrimaryBank q 3 (recohCanonicalPrimaryData q 3) j) B =
          recohSupportProbe (recohCyclicPrimaryBank q 3 (recohCanonicalPrimaryData q 3) j) C →
            OrdinaryPartner B C := by
  simp only [recohTernaryOrbitCheck, recohOrbitSeparatorCheck, decide_eq_true_eq]
  constructor
  · intro h B hB C hC heq
    rcases h B hB C hC with ho | hn
    · exact (recoh_torsion_orbit_check_iff B C (hnonempty B hB)).mp ho
    · exact (hn ((recoh_ternary_reading_equal_iff q j B C).mpr heq)).elim
  · intro h B hB C hC
    by_cases heq : recohTernaryReadingEqual q j B C = true
    · exact Or.inl ((recoh_torsion_orbit_check_iff B C (hnonempty B hB)).mpr
        (h B hB C hC ((recoh_ternary_reading_equal_iff q j B C).mp heq)))
    · exact Or.inr heq

/-- The optional extra coordinate depends only on the labelled square.
Its finite scan follows the increasing order of presentation coordinates. -/
def recohSquareTernaryChoice
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    Option (RecohPrimaryCoordinate q 3) :=
  let reps := recohCyclicSquareRepresentatives q entries
  if recohOneOrbitCheck reps then none
  else recohFirstPassing (recohTernaryOrbitCheck q reps) (Finset.univ.sort (· ≤ ·))



theorem recoh_cyclic_square_representatives_sound
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (B : Finset ((i : Fin d) → ZMod (q i)))
    (hB : B ∈ recohCyclicSquareRepresentatives q entries) :
    B.card = 3 ∧ orderedSquare B = recohTypedSquareValue entries :=
  recoh_square_representatives_sound _ _ _ (recoh_selected_square_support_covered q entries) B hB

theorem recoh_cyclic_square_representatives_nonempty
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (B : Finset ((i : Fin d) → ZMod (q i)))
    (hB : B ∈ recohCyclicSquareRepresentatives q entries) : B.Nonempty := by
  apply Finset.card_pos.mp
  rw [(recoh_cyclic_square_representatives_sound q entries B hB).1]
  decide













end Cyclic

end Couret.STROBO2TORS


