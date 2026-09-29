-- Prove2me | solution 1 for ExternalInterpretationLogicalInvariance.exists_perm_of_kernel_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:11:31.41856+00:00
-- url     : https://prove2.me/submissions/46c73e5f-72d4-4934-bdca-53c67e7d47a4

-- Sol generated from Applications/ExternalInterpretationLogicalInvariance.lean
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



/-! ## Part C — Binary interpretations: only equality survives -/




/-! ### Sharpness: the arity must be finite -/




/-! ## Part D — Quantitative meaning loss -/

variable {G : Type u} {M : Type v} {V : Type w} [Group G] [MulAction G M]





open ExternalInterpretationLogicalInvariance in
theorem solution{α : Type u} {ι : Type v} [Finite ι] (f g : ι → α)
    (hker : ∀ i j, f i = f j ↔ g i = g j) : ∃ σ : Equiv.Perm α, ∀ i, σ (f i) = g i := by
  classical
  have hinj : Function.Injective (fun a : (Set.range f) => g (Classical.choose a.2)) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have h1 : f (Classical.choose ha) = a := Classical.choose_spec ha
    have h2 : f (Classical.choose hb) = b := Classical.choose_spec hb
    have hf := (hker _ _).mpr hab
    simp only [Subtype.mk.injEq]
    rw [← h1, ← h2, hf]
  let emb : (Set.range f) ↪ α := ⟨fun a => g (Classical.choose a.2), hinj⟩
  have hex : ∃ σ : α ≃ α, ∀ x : (Set.range f), σ x = emb x := by
    cases finite_or_infinite α with
    | inl _ => exact Cardinal.extend_function_finite emb ⟨Equiv.refl α⟩
    | inr _ =>
      refine Cardinal.extend_function_of_lt emb ?_ ⟨Equiv.refl α⟩
      have hfin : (Set.range f).Finite := Set.finite_range f
      calc Cardinal.mk (Set.range f) < Cardinal.aleph0 := Cardinal.lt_aleph0_of_finite _
        _ ≤ Cardinal.mk α := Cardinal.aleph0_le_mk α
  obtain ⟨σ, hσ⟩ := hex
  refine ⟨σ, fun i => ?_⟩
  have hmem : f i ∈ Set.range f := ⟨i, rfl⟩
  have hval := hσ ⟨f i, hmem⟩
  simp only [emb, Function.Embedding.coeFn_mk] at hval
  rw [hval]
  exact (hker _ _).mp (Classical.choose_spec hmem)
