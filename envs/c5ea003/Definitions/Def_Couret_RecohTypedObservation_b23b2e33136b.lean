-- Prove2me | Definitions.Def_Couret_RecohTypedObservation_b23b2e33136b
-- name    : Couret_RecohTypedObservation_b23b2e33136b
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:04:38.080612+00:00
-- url     : https://prove2.me/theorems/52bcb15e-6409-4cf7-b7a8-e4b10b877201
-- title:
--   Typed sparse square observations
-- statement:
--   A typed square observation is a list of pairs $(z,m)$; its support is the set of listed points, and its value at $z$ sums all multiplicities listed there. Its format requires three to six entries, no repeated points, multiplicities between one and three, total multiplicity nine, and exactly one or three odd multiplicities.
--
--   The bundle also defines executable square-format validation and simultaneous validation of sparse coefficient formats over a finite index set. These constraints match the supported triple-square input representation.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohTypedObservation.lean; source file SHA-256 5e7a00f9666a5b8cb41765e60b981ccdb33bfeadfb65f8a536d67383af84ce84

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
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCoefficientObservations_4ffca285ab72

set_option autoImplicit false

/-!
Typed sparse input for the labelled ordered convolution square.

The coefficient function and its covering finite set are constructed from
the same list of position/count entries.  Their consistency is proved,
rather than supplied to the decoder.  The format validator expresses the
numeric checks performed by the Python square reader after coordinates and
integers have been parsed.  Syntactic JSON parsing is not part of this file.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [DecidableEq G]

/-- Nonzero values can occur only at a position explicitly supplied. -/
def recohTypedSquareSupport (entries : List (G × ℕ)) : Finset G :=
  (entries.map Prod.fst).toFinset

/-- Interpretation of a sparse labelled square, also defined for duplicate
positions by adding their counts.  The external format disallows duplicates. -/
def recohTypedSquareValue (entries : List (G × ℕ)) (z : G) : ℕ :=
  ((entries.filter (fun t => t.1 = z)).map Prod.snd).sum

theorem recoh_typed_square_zero_outside
    (entries : List (G × ℕ)) (z : G)
    (hz : z ∉ recohTypedSquareSupport entries) : recohTypedSquareValue entries z = 0 := by
  have hf : entries.filter (fun t => t.1 = z) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro t ht
    have ht' := List.mem_filter.mp ht
    have he : t.1 = z := by simpa using ht'.2
    apply hz
    simp only [recohTypedSquareSupport, List.mem_toFinset, List.mem_map]
    exact ⟨t, ht'.1, he⟩
  simp [recohTypedSquareValue, hf]

theorem recoh_typed_square_covered
    (entries : List (G × ℕ)) (z : G)
    (hz : recohTypedSquareValue entries z ≠ 0) : z ∈ recohTypedSquareSupport entries := by
  by_contra hn
  exact hz (recoh_typed_square_zero_outside entries z hn)

/-- The scalar constraints of the Python square parser on typed entries.
The position order is unrestricted, and the full ordered mass is nine. -/
def RecohTypedSquareFormat (entries : List (G × ℕ)) : Prop :=
  3 ≤ entries.length ∧ entries.length ≤ 6 ∧
    (entries.map Prod.fst).Nodup ∧
    (∀ t ∈ entries, 1 ≤ t.2 ∧ t.2 ≤ 3) ∧
    (entries.map Prod.snd).sum = 9 ∧
    (((entries.map (fun t => t.2 % 2)).sum = 1) ∨
      ((entries.map (fun t => t.2 % 2)).sum = 3))

instance recohTypedSquareFormatDecidable (entries : List (G × ℕ)) :
    Decidable (RecohTypedSquareFormat entries) := by
  unfold RecohTypedSquareFormat
  infer_instance

/-- Executable validation of the typed sparse square. -/
def recohTypedSquareFormatCheck (entries : List (G × ℕ)) : Bool :=
  decide (RecohTypedSquareFormat entries)





/-- A single runtime guard for all typed coefficient lists. -/
def recohAllCoefficientFormats {I : Type*} [Fintype I]
    (p k : I → ℕ) (terms : I → RecohSparseTerms) : Bool :=
  decide (∀ i, recohCoefficientFormatCheck (p i) (k i) (terms i) = true)



end Couret.STROBO2TORS


