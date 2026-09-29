-- Prove2me | Theorems.Thm_MatroidMinorBridge_finite_forbidden_minor_characterization
-- name    : MatroidMinorBridge.finite_forbidden_minor_characterization
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:07:22.957372+00:00
-- url     : https://prove2.me/theorems/858d59f0-c241-42cb-8859-ba51905fde4f
-- title:
--   Finite forbidden-minor bridge.
-- statement:
--   **Finite forbidden-minor bridge.** If the containment/minor order is a
--   well-quasi-order, every minor-closed class is characterized by finitely many
--   excluded objects.
--
--   This is the precise logical connection used to pass from a Robertson--Seymour
--   style sequence theorem to a finite forbidden-minor theorem.
--
--   ```lean
--   theorem MatroidMinorBridge.finite_forbidden_minor_characterization[WellQuasiOrderedLE α]
--       (Good : α → Prop)
--       (hdown : ∀ ⦃a b : α⦄, a ≤ b → Good b → Good a) :
--       ∃ forbidden : Finset α,
--         (∀ e ∈ forbidden, IsExcluded Good e) ∧
--         ∀ x, Good x ↔ ∀ e ∈ forbidden, ¬ e ≤ x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/MatroidMinorFiniteObstructions.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/MatroidMinorFiniteObstructions.lean#L43

-- Thm stub generated from Novelty/MatroidMinorFiniteObstructions.lean
import Mathlib
import Definitions.Def_Novelty_MatroidMinorFiniteObstructions
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

open MatroidMinorBridge

variable {α : Type*} [PartialOrder α]

theorem MatroidMinorBridge.finite_forbidden_minor_characterization[WellQuasiOrderedLE α]
    (Good : α → Prop)
    (hdown : ∀ ⦃a b : α⦄, a ≤ b → Good b → Good a) :
    ∃ forbidden : Finset α,
      (∀ e ∈ forbidden, IsExcluded Good e) ∧
      ∀ x, Good x ↔ ∀ e ∈ forbidden, ¬ e ≤ x := by sorry
