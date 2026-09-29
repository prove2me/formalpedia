-- Prove2me | Definitions.Def_Geometry_OvalArrangement
-- name    : Geometry_OvalArrangement
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:45:31.190887+00:00
-- url     : https://prove2.me/theorems/e67807ae-b9bb-4237-8dee-7702e6eeb0e6
-- title:
--   Aether Catalog definitions — Geometry_OvalArrangement
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.OvalArrangement`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/OvalArrangement.lean by skeleton subtraction
import Mathlib
/-
# Oval Arrangements and Nesting Forest Structure

This file formalizes the combinatorial topology of oval arrangements on smooth
real plane algebraic curves. The central result is that the nesting relation
among ovals (connected components of the real locus) forms a forest, and that
various combinatorial invariants of this forest are constrained by the Harnack bound.

## Main definitions

* `OvalArrangement` — A finite set of ovals with a nesting strict partial order
  satisfying the forest property (every principal downset is totally ordered).

* `NestingForest` — Type alias emphasizing the forest structure.

* `nestingDepth` — Maximum chain length in the nesting order.

## Main results

* `OvalArrangement.card_le_genus_add_one` — The number of ovals is at most `g + 1`.
* `OvalArrangement.depth_le_half_degree` — Nesting depth ≤ ⌊d/2⌋.
* `OvalArrangement.outerOvals_pos` — There exists at least one outermost oval.
* `OvalArrangement.inner_outer_parity` — Ovals at even depth are outer,
  ovals at odd depth are inner.

## Mathematical context

For a smooth real plane algebraic curve of degree `d`, the real locus consists of
at most `g + 1 = (d-1)(d-2)/2 + 1` ovals (closed embedded curves homeomorphic to S¹)
by the Harnack bound. Each oval bounds a disk in ℝP², and the nesting relation
"oval A lies in the interior of oval B" is a strict partial order. The key topological
fact is that this order has the **forest property**: for any two ovals A, B that both
contain a third oval C, either A contains B or B contains A. This makes the nesting
relation a rooted forest, where the roots are the outermost ovals.

The nesting forest is a fundamental invariant in the classification of real algebraic
curves, central to Hilbert's 16th problem. Gudkov's conjecture (proved by
Rokhlin, 1972) and subsequent work constrain which forests can be realized.
-/


namespace Hilbert16

/-! ## Forest Partial Orders

A forest partial order is a partial order where the downward closure of every
element is totally ordered. Equivalently, every two elements with a common
upper bound are comparable. -/

/-- A forest order on a finite type: a partial order where every principal
    downset (predecessors of an element) is totally ordered.
    This captures the essential property of nesting among ovals:
    if both A and B contain C, then A ⊆ B or B ⊆ A. -/
class ForestOrder (α : Type*) extends PartialOrder α where
  /-- Every downset is totally ordered: if a ≤ c and b ≤ c then a ≤ b or b ≤ a -/
  downset_linear : ∀ {a b c : α}, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a



/-! ## Oval Arrangements -/

/-- An oval arrangement for a smooth real plane curve of degree `d`.
    This packages:
    - A finite type of ovals
    - A forest order (nesting relation)
    - The degree and genus data
    - The Harnack bound constraint -/
structure OvalArrangement where
  /-- Degree of the defining polynomial -/
  degree : ℕ
  /-- Number of ovals -/
  numOvals : ℕ
  /-- Harnack bound: numOvals ≤ genus + 1 -/
  harnack : numOvals ≤ (degree - 1) * (degree - 2) / 2 + 1
  /-- Nesting depth: length of the longest chain in the forest -/
  nestingDepth : ℕ
  /-- Depth bound: nesting depth ≤ ⌊d/2⌋ -/
  depth_bound : nestingDepth ≤ degree / 2
  /-- Number of outermost (root) ovals -/
  numRoots : ℕ
  /-- Every oval arrangement with ovals has at least one root -/
  roots_pos : 0 < numOvals → 0 < numRoots
  /-- Roots are ovals -/
  roots_le : numRoots ≤ numOvals

/-- The genus of the underlying curve. -/
def OvalArrangement.genus (A : OvalArrangement) : ℕ :=
  (A.degree - 1) * (A.degree - 2) / 2



/-! ## Combinatorial constraints on oval arrangements -/





/-! ## Nesting forest on a Finset with explicit parent function

For computational purposes, we also define a concrete forest structure
using a parent function. -/

/-- A concrete nesting forest on `Fin n` using a partial parent function.
    Each oval either has a unique parent (the immediately enclosing oval)
    or is a root (outermost oval). -/
structure ConcNestingForest (n : ℕ) where
  /-- Parent function: `parent i = some j` means oval `i` is immediately inside oval `j`.
      `parent i = none` means oval `i` is a root (outermost). -/
  parent : Fin n → Option (Fin n)
  /-- No oval is its own parent -/
  no_self_parent : ∀ i, parent i ≠ some i
  /-- The depth of each oval (longest chain to a root) -/
  depth : Fin n → ℕ
  /-- Roots have depth 0 -/
  root_depth : ∀ i, parent i = none → depth i = 0
  /-- Children have depth one more than parent -/
  child_depth : ∀ i j, parent i = some j → depth i = depth j + 1




/-! ## Inner and outer ovals -/

/-- An oval is outer (even) if its depth is even, inner (odd) if its depth is odd.
    For a dividing curve, outer ovals bound regions on both sides;
    for a non-dividing curve, the parity still determines orientation behavior. -/
def ConcNestingForest.isOuter {n : ℕ} (F : ConcNestingForest n) (i : Fin n) : Prop :=
  F.depth i % 2 = 0

/-- An oval is inner if it is not outer. -/
def ConcNestingForest.isInner {n : ℕ} (F : ConcNestingForest n) (i : Fin n) : Prop :=
  F.depth i % 2 = 1




end Hilbert16


