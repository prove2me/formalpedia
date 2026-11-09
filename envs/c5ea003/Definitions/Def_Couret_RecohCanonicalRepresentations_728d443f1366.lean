-- Prove2me | Definitions.Def_Couret_RecohCanonicalRepresentations_728d443f1366
-- name    : Couret_RecohCanonicalRepresentations_728d443f1366
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:05:59.324045+00:00
-- url     : https://prove2.me/theorems/b1124711-e7f2-4775-bc4c-319647320738
-- title:
--   Canonical coordinates and ordered-pair counters
-- statement:
--   For nonzero moduli $q_i$, canonical points use coordinates $0\le x_i<q_i$. Encoding and decoding connect them to $\prod_i\mathbb Z/q_i$, while addition, subtraction and doubling reduce coordinatewise modulo $q_i$. Lists of pair sums retain all ordered multiplicities, with counters recording $$N(z)=|\{(x,y):x+y=z\}|.$$ This matches executable coordinate and counter operations.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCanonicalRepresentations.lean; source file SHA-256 316b02d78efff655bcc676d7681a06d198da79e90c819ec51ee6c7d5bb423e8e

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
import Definitions.Def_Couret_RecohTypedObservation_b23b2e33136b
import Definitions.Def_Couret_RecohCyclicPrimaryBank_92b8732c410a

set_option autoImplicit false

/-!
Canonical numeric points and ordered counters for the Python v0.2 boundary.

A typed point has one natural coordinate strictly below each nonzero modulus.
The maps below construct the correspondence with the product of `ZMod`s;
no interpretation hypothesis is supplied by a caller.  The arithmetic is the
modular arithmetic used by `_add`, `_sub`, and `_double`.  The list counter
counts all ordered pairs, including the diagonal and repeated resulting sums.

This module does not model Python objects, tuple sorting, JSON parsing,
exceptions, or execution of the Python interpreter.  In particular, the
no-duplicate hypothesis on a support is essential when a list is replaced by
a finite set.
-/

namespace Couret.STROBO2TORS

section Coordinates

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

/-- Already parsed, in-range natural coordinates. -/
abbrev RecohCanonicalPoint := (i : Fin d) → Fin (q i)

/-- Interpret the canonical natural representatives in the cyclic product. -/
def recohPointEncode (x : RecohCanonicalPoint q) : (i : Fin d) → ZMod (q i) :=
  fun i => (x i).val

/-- Select the canonical natural representative of every residue. -/
def recohPointDecode (x : (i : Fin d) → ZMod (q i)) : RecohCanonicalPoint q :=
  fun i => ⟨(x i).val, ZMod.val_lt (x i)⟩









/-- The coordinatewise `% n` addition used by `_add`. -/
def recohPointAdd (x y : RecohCanonicalPoint q) : RecohCanonicalPoint q :=
  fun i => ⟨((x i).val + (y i).val) % q i, Nat.mod_lt _ (NeZero.pos (q i))⟩

/-- A natural-number expression for canonical modular subtraction.  Adding
one modulus before subtracting is valid because the second coordinate is in
range; it has the same residue as Python's signed subtraction followed by `%`. -/
def recohPointSub (x y : RecohCanonicalPoint q) : RecohCanonicalPoint q :=
  fun i => ⟨(q i + (x i).val - (y i).val) % q i,
    Nat.mod_lt _ (NeZero.pos (q i))⟩

/-- The coordinatewise doubling used by `_double`. -/
def recohPointDouble (x : RecohCanonicalPoint q) : RecohCanonicalPoint q :=
  fun i => ⟨(2 * (x i).val) % q i, Nat.mod_lt _ (NeZero.pos (q i))⟩















end Coordinates

section ListCounters

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Explicit enumeration of ordered list pairs; duplicate sums are retained. -/
def recohListPairSums (xs ys : List G) : List G :=
  xs.flatMap (fun x => ys.map (fun y => x + y))

/-- The exact multiplicity computed by an ordered-pair `Counter`. -/
def recohListCounter (xs : List G) (z : G) : ℕ :=
  (recohListPairSums xs xs).count z



















end ListCounters

section CanonicalCounters

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

/-- Ordered modular sums on canonical coordinate tuples. -/
def recohCanonicalPairSums (xs ys : List (RecohCanonicalPoint q)) :
    List (RecohCanonicalPoint q) :=
  xs.flatMap (fun x => ys.map (recohPointAdd q x))

def recohCanonicalCounter (xs : List (RecohCanonicalPoint q))
    (z : RecohCanonicalPoint q) : ℕ :=
  (recohCanonicalPairSums q xs xs).count z











end CanonicalCounters

end Couret.STROBO2TORS


