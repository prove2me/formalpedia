-- Prove2me | Theorems.Thm_Catalog_Novelty_QuantumTopoMitigation_threshold_iff_of_noise_margin
-- name    : Catalog.Novelty.QuantumTopoMitigation.threshold_iff_of_noise_margin
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:16:34.39907+00:00
-- url     : https://prove2.me/theorems/48174831-828a-473a-b224-76f4435893c1
-- title:
--   Threshold iff of noise margin
-- statement:
--   Formal statement of `Catalog.Novelty.QuantumTopoMitigation.threshold_iff_of_noise_margin` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Catalog.Novelty.QuantumTopoMitigation.threshold_iff_of_noise_margin{x y τ ε m : ℝ}
--       (hnoise : |x - y| ≤ ε) (hmargin : m ≤ |y - τ|) (hsep : 2 * ε < m) :
--       (τ < x ↔ τ < y) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ErrorMitigation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ErrorMitigation.lean#L36

-- Thm stub generated from Novelty/ErrorMitigation.lean
import Mathlib
import Definitions.Def_Novelty_ErrorMitigation

/-!
# Quantum-topological error mitigation: barcodes and persistence

This file provides the basic data model shared by the error-mitigation development:
a finite-data model of a persistence *bar* and its persistence value, together with
a pointwise threshold-stability lemma.

The mathematical content is intentionally elementary: a `Bar` is just a birth/death
pair of real numbers, and its `persistence` is the length `death - birth`.  The key
analytic fact, `threshold_iff_of_noise_margin`, says that if a noisy persistence value
`x` is within `ε` of the true value `y`, and the true value is separated from a
threshold `τ` by a margin `m` exceeding `2 * ε`, then `x` and `y` lie on the same side
of `τ`.

This file does **not** import `Betti.lean`; the dependency may only go the other way.
-/

open Catalog.Novelty.QuantumTopoMitigation



/-
**Pointwise threshold stability.**  If the noisy value `x` is within `ε` of the
true value `y`, and `y` is separated from the threshold `τ` by a margin `m` with
`2 * ε < m`, then `x` and `y` lie on the same side of `τ`.
-/

theorem Catalog.Novelty.QuantumTopoMitigation.threshold_iff_of_noise_margin{x y τ ε m : ℝ}
    (hnoise : |x - y| ≤ ε) (hmargin : m ≤ |y - τ|) (hsep : 2 * ε < m) :
    (τ < x ↔ τ < y) := by sorry
