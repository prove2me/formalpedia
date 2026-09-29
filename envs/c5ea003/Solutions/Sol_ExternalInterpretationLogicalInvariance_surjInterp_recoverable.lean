-- Prove2me | solution 1 for ExternalInterpretationLogicalInvariance.surjInterp_recoverable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:11:32.015897+00:00
-- url     : https://prove2.me/submissions/589f4d46-f8a4-48b3-8d45-dff55d6b52af

-- Sol generated from Applications/ExternalInterpretationLogicalInvariance.lean
import Mathlib
import Definitions.Def_Applications_ExternalInterpretationDefinability
import Definitions.Def_Applications_ExternalInterpretationLogicalInvariance
import Theorems.Thm_ExternalInterpretationDefinability_recoverable_iff_orbitConstant
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



/-! ## Part C — Binary interpretations: only equality survives -/




/-! ### Sharpness: the arity must be finite -/




/-! ## Part D — Quantitative meaning loss -/

variable {G : Type u} {M : Type v} {V : Type w} [Group G] [MulAction G M]





open ExternalInterpretationLogicalInvariance in
theorem solution: Recoverable (Equiv.Perm ℕ) surjInterp := by
  rw [recoverable_iff_orbitConstant]
  rintro f g ⟨σ, rfl⟩
  have hiff : Function.Surjective f ↔ Function.Surjective (σ • f) := by
    constructor
    · intro hf n
      obtain ⟨m, hm⟩ := hf (σ.symm n)
      exact ⟨m, by show σ (f m) = n; rw [hm]; simp⟩
    · intro hf n
      obtain ⟨m, hm⟩ := hf (σ n)
      have : σ (f m) = σ n := hm
      exact ⟨m, σ.injective this⟩
  exact propext hiff
