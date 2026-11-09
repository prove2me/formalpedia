-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_canonical_counter_equal_iff
-- name    : Couret.STROBO2TORS.recoh_canonical_counter_equal_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:53:05.993119+00:00
-- url     : https://prove2.me/theorems/1388c442-a866-4caf-9809-a3bc257d88f9
-- title:
--   Canonical tuple counters exactly represent ordered squares
-- statement:
--   Let $d\in\mathbb N$, let $q_0,\ldots,q_{d-1}$ be positive integers, and put $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$. Let $L,M$ be duplicate-free lists of canonical coordinate tuples, and let $S,T$ be their encoded supports in $G$. The canonical counter counts all ordered pair sums as canonical tuples. Then
--
--   $$\operatorname{Counter}(L)=\operatorname{Counter}(M)\Longleftrightarrow Q_S=Q_T.$$
--
--   This transports equality of executable counters to the group-theoretic square data.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCanonicalRepresentations.lean, lines 264–283; source file SHA-256 316b02d78efff655bcc676d7681a06d198da79e90c819ec51ee6c7d5bb423e8e; theorem Couret.STROBO2TORS.recoh_canonical_counter_equal_iff

import Aesop
import Definitions.Def_Couret_RecohCanonicalRepresentations_728d443f1366
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



































end Coordinates

section ListCounters

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























end ListCounters

section CanonicalCounters

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

theorem recoh_canonical_counter_equal_iff
    (xs ys : List (RecohCanonicalPoint q)) (hxs : xs.Nodup) (hys : ys.Nodup) :
    recohCanonicalCounter q xs = recohCanonicalCounter q ys ↔
      orderedSquare (xs.map (recohPointEncode q)).toFinset =
        orderedSquare (ys.map (recohPointEncode q)).toFinset := by sorry


end CanonicalCounters

end Couret.STROBO2TORS
