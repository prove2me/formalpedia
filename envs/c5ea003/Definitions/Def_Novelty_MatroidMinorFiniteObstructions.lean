-- Prove2me | Definitions.Def_Novelty_MatroidMinorFiniteObstructions
-- name    : Novelty_MatroidMinorFiniteObstructions
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:32:28.435155+00:00
-- url     : https://prove2.me/theorems/46f4846f-ef9f-4236-a7f6-abe33469406b
-- title:
--   Aether Catalog definitions — Novelty_MatroidMinorFiniteObstructions
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.MatroidMinorFiniteObstructions`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/MatroidMinorFiniteObstructions.lean by skeleton subtraction
import Mathlib
import Mathlib.Order.WellFoundedSet

/-!
# From well-quasi-ordering to finite forbidden-minor descriptions

This file isolates the order-theoretic bridge underlying forbidden-minor theorems.
An object `a` is read as a minor of `b` when `a ≤ b`.  A class `Good` is
minor-closed when it is downward closed.  The theorem proves that a
well-quasi-order forces every such class to have a finite obstruction set.

The result is deliberately abstract: it applies to graphs, matroids, words under
embedding, and other containment orders.  It does not assume the unresolved
well-quasi-ordering statement for finite-field-representable matroids.
-/

namespace MatroidMinorBridge

variable {α : Type*} [PartialOrder α]

/-- The minimal objects outside a downward-closed class. -/
def IsExcluded (Good : α → Prop) (x : α) : Prop :=
  ¬ Good x ∧ ∀ y, y < x → Good y




end MatroidMinorBridge


