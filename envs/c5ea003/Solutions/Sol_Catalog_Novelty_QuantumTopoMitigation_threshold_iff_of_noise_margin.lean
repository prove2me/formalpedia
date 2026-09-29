-- Prove2me | solution 1 for Catalog.Novelty.QuantumTopoMitigation.threshold_iff_of_noise_margin
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:21:28.125176+00:00
-- url     : https://prove2.me/submissions/e3cc6f87-57f8-46a1-89cf-bb662f991cf6

-- Sol generated from Novelty/ErrorMitigation.lean
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


open Catalog.Novelty.QuantumTopoMitigation in
theorem solution{x y τ ε m : ℝ}
    (hnoise : |x - y| ≤ ε) (hmargin : m ≤ |y - τ|) (hsep : 2 * ε < m) :
    (τ < x ↔ τ < y) := by
      constructor <;> intro h <;> cases abs_cases ( x - y ) <;> cases abs_cases ( y - τ ) <;> linarith
