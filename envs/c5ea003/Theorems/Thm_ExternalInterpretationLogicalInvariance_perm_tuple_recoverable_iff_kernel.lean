-- Prove2me | Theorems.Thm_ExternalInterpretationLogicalInvariance_perm_tuple_recoverable_iff_kernel
-- name    : ExternalInterpretationLogicalInvariance.perm_tuple_recoverable_iff_kernel
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:52:14.953149+00:00
-- url     : https://prove2.me/theorems/a41d69bb-d75e-40f9-ba79-bfccdb179ae4
-- title:
--   Logical invariance theorem.
-- statement:
--   **Logical invariance theorem.**  For a model `α` carrying no structure beyond
--   equality (so that the automorphism group is the full symmetric group), an
--   external interpretation of tuples with finitely many coordinates is recoverable
--   from structural truth exactly when it depends only on the kernel of the tuple:
--   only equality is logical.
--
--   ```lean
--   theorem ExternalInterpretationLogicalInvariance.perm_tuple_recoverable_iff_kernel{α : Type u} {ι : Type v} [Finite ι] {V : Type w}
--       (I : (ι → α) → V) :
--       Recoverable (Equiv.Perm α) I ↔
--         ∀ f g : ι → α, (∀ i j, f i = f j ↔ g i = g j) → I f = I g := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/ExternalInterpretationLogicalInvariance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/ExternalInterpretationLogicalInvariance.lean#L78

-- Thm stub generated from Applications/ExternalInterpretationLogicalInvariance.lean
import Mathlib
import Definitions.Def_Applications_ExternalInterpretationDefinability
import Definitions.Def_Applications_ExternalInterpretationLogicalInvariance
/-
# The Definability Boundary, III: Logical Invariance and Quantitative Meaning Loss

This file continues `Catalog/Applications/ExternalInterpretationDefinability.lean`
and `Catalog/Applications/ExternalInterpretationGraphs.lean`.

The previous files classified *unary* external interpretations.  Here we push the
classification to interpretations of **tuples**, where the answer becomes a sharp
syntactic statement: under the full symmetric group of a model of *any*
cardinality, an interpretation of finitely many coordinates is recoverable from
structural truth exactly when it depends only on the *kernel* of the tuple — i.e.
only on which coordinates are equal.  This is the formal form of the classical
dictum that the only purely logical (permutation-invariant) notions are the ones
built from equality.  The finiteness of the *arity* is essential and is shown to
be so.

* **Part A — Transport.**  `exists_perm_of_kernel_eq` : two finitely-indexed
  tuples with the same equality pattern are carried onto each other by a
  permutation of the carrier (built by extending the induced bijection between
  their finite ranges, splitting on whether the carrier is finite or infinite).
* **Part B — Logical invariance.**  `perm_tuple_recoverable_iff_kernel` : a tuple
  interpretation is recoverable iff it factors through the kernel; and
  `kernel_classification_fails_for_infinite_arity` shows that for infinitely many
  coordinates this fails — surjectivity of a sequence is recoverable but not
  kernel-determined.
* **Part C — Binary case and a concrete collision.**  `perm_pair_recoverable_iff`
  specialises to binary interpretations: only equality survives.  Consequently
  the *order* relation on `Fin 3` is not recoverable
  (`lt_not_recoverable`) — the meaning-collision phenomenon at the level of
  relations rather than points.
* **Part D — Quantitative meaning loss.**  `card_interpretations_split` factors
  the total number of interpretations as (recoverable ones) × (a pure loss
  factor), and `card_recoverable_lt` shows the loss is strict as soon as one
  orbit is non-trivial and there are at least two meanings.
-/


open ExternalInterpretationLogicalInvariance

open MulAction ExternalInterpretationDefinability

universe u v w

/-! ## Part A — Transporting tuples with the same equality pattern -/


/-! ## Part B — Logical invariance for tuple interpretations -/

theorem ExternalInterpretationLogicalInvariance.perm_tuple_recoverable_iff_kernel{α : Type u} {ι : Type v} [Finite ι] {V : Type w}
    (I : (ι → α) → V) :
    Recoverable (Equiv.Perm α) I ↔
      ∀ f g : ι → α, (∀ i j, f i = f j ↔ g i = g j) → I f = I g := by sorry
