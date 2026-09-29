-- Prove2me | solution 1 for ExternalInterpretationLogicalInvariance.kernel_classification_fails_for_infinite_arity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:15:45.437357+00:00
-- url     : https://prove2.me/submissions/192f9a9d-9466-490c-ad03-3a49dc42f488

-- Sol generated from Applications/ExternalInterpretationLogicalInvariance.lean
import Mathlib
import Definitions.Def_Applications_ExternalInterpretationDefinability
import Definitions.Def_Applications_ExternalInterpretationLogicalInvariance
import Theorems.Thm_ExternalInterpretationLogicalInvariance_surjInterp_recoverable
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
theorem solution:
    Recoverable (Equiv.Perm ℕ) surjInterp ∧
      ¬ (∀ f g : ℕ → ℕ, (∀ i j, f i = f j ↔ g i = g j) → surjInterp f = surjInterp g) := by
  refine ⟨surjInterp_recoverable, ?_⟩
  intro h
  have hker : ∀ i j : ℕ, (2 * i = 2 * j) ↔ (id i = id j) := by
    intro i j
    show 2 * i = 2 * j ↔ i = j
    omega
  have heq := h (fun n => 2 * n) id hker
  have hid : surjInterp id := fun n => ⟨n, rfl⟩
  have hnot : ¬ surjInterp (fun n => 2 * n) := by
    intro hs
    obtain ⟨m, hm⟩ := hs 1
    have : 2 * m = 1 := hm
    omega
  rw [heq] at hnot
  exact hnot hid
