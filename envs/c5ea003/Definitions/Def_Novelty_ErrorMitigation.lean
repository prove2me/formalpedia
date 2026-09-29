-- Prove2me | Definitions.Def_Novelty_ErrorMitigation
-- name    : Novelty_ErrorMitigation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:06:56.031328+00:00
-- url     : https://prove2.me/theorems/65e7a064-e29c-490b-9f5f-3d1ad92ab334
-- title:
--   Aether Catalog definitions — Novelty_ErrorMitigation
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ErrorMitigation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ErrorMitigation.lean by skeleton subtraction
import Mathlib

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

namespace Catalog.Novelty.QuantumTopoMitigation

/-- A persistence *bar*: a birth time and a death time. -/
structure Bar where
  /-- The birth time of the topological feature. -/
  birth : ℝ
  /-- The death time of the topological feature. -/
  death : ℝ

/-- The persistence (lifetime) of a bar. -/
def persistence (b : Bar) : ℝ := b.death - b.birth

/-
**Pointwise threshold stability.**  If the noisy value `x` is within `ε` of the
true value `y`, and `y` is separated from the threshold `τ` by a margin `m` with
`2 * ε < m`, then `x` and `y` lie on the same side of `τ`.
-/

end Catalog.Novelty.QuantumTopoMitigation


