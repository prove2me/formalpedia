-- Prove2me | solution 1 for ExternalInterpretationLogicalInvariance.perm_pair_recoverable_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:15:45.907863+00:00
-- url     : https://prove2.me/submissions/50dee4b9-70b4-4509-87d5-d88e6caa3115

-- Sol generated from Applications/ExternalInterpretationLogicalInvariance.lean
import Mathlib
import Definitions.Def_Applications_ExternalInterpretationDefinability
import Definitions.Def_Applications_ExternalInterpretationLogicalInvariance
import Theorems.Thm_ExternalInterpretationDefinability_recoverable_iff_orbitConstant
import Theorems.Thm_ExternalInterpretationLogicalInvariance_exists_perm_of_kernel_eq
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
theorem solution{α : Type u} {V : Type w} (I : α × α → V) :
    Recoverable (Equiv.Perm α) I ↔
      ∀ p q : α × α, (p.1 = p.2 ↔ q.1 = q.2) → I p = I q := by
  rw [recoverable_iff_orbitConstant]
  constructor
  · rintro h ⟨x, y⟩ ⟨u, v⟩ hpat
    have hk : ∀ i j : Fin 2,
        (![x, y] : Fin 2 → α) i = ![x, y] j ↔ (![u, v] : Fin 2 → α) i = ![u, v] j := by
      intro i j
      fin_cases i <;> fin_cases j
      · exact ⟨fun _ => rfl, fun _ => rfl⟩
      · exact hpat
      · exact ⟨fun hh => (hpat.mp hh.symm).symm, fun hh => (hpat.mpr hh.symm).symm⟩
      · exact ⟨fun _ => rfl, fun _ => rfl⟩
    obtain ⟨σ, hσ⟩ := exists_perm_of_kernel_eq (![x, y] : Fin 2 → α) ![u, v] hk
    refine h ⟨σ, ?_⟩
    have h0 := hσ 0
    have h1 := hσ 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    show ((σ x, σ y) : α × α) = (u, v)
    rw [h0, h1]
  · rintro h ⟨x, y⟩ q ⟨σ, rfl⟩
    refine h (x, y) (σ • (x, y)) ?_
    show x = y ↔ σ x = σ y
    exact ⟨fun hh => by rw [hh], fun hh => σ.injective hh⟩
