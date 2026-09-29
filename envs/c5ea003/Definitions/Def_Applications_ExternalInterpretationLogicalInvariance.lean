-- Prove2me | Definitions.Def_Applications_ExternalInterpretationLogicalInvariance
-- name    : Applications_ExternalInterpretationLogicalInvariance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:45:59.663085+00:00
-- url     : https://prove2.me/theorems/4dabbe9d-df81-452c-a33e-9195f11b599d
-- title:
--   Aether Catalog definitions — Applications_ExternalInterpretationLogicalInvariance
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ExternalInterpretationLogicalInvariance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ExternalInterpretationLogicalInvariance.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_ExternalInterpretationDefinability
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


namespace ExternalInterpretationLogicalInvariance

open MulAction ExternalInterpretationDefinability

universe u v w

/-! ## Part A — Transporting tuples with the same equality pattern -/


/-! ## Part B — Logical invariance for tuple interpretations -/



/-! ## Part C — Binary interpretations: only equality survives -/




/-! ### Sharpness: the arity must be finite -/

/-- The surjectivity interpretation of infinite sequences of naturals. -/
def surjInterp : (ℕ → ℕ) → Prop := fun f => Function.Surjective f



/-! ## Part D — Quantitative meaning loss -/

variable {G : Type u} {M : Type v} {V : Type w} [Group G] [MulAction G M]




end ExternalInterpretationLogicalInvariance


