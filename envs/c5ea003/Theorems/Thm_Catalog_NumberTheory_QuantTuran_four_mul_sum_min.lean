-- Prove2me | Theorems.Thm_Catalog_NumberTheory_QuantTuran_four_mul_sum_min
-- name    : Catalog.NumberTheory.QuantTuran.four_mul_sum_min
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:25:06.750315+00:00
-- url     : https://prove2.me/theorems/18c14dfa-0580-4171-8695-819d8e616ad1
-- title:
--   Division-free form of the `L¹` energy.
-- statement:
--   **Division-free form of the `L¹` energy.**
--
--   ```lean
--   theorem Catalog.NumberTheory.QuantTuran.four_mul_sum_min(q : ℕ) :
--       4 * ∑ j ∈ Finset.range q, min j (q - j) + q % 2 = q ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/QuantL1TuranBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/QuantL1TuranBridge.lean#L147

-- Thm stub generated from NumberTheory/QuantL1TuranBridge.lean
import Mathlib
import Definitions.Def_NumberTheory_QuantL1TuranBridge
/-
# The `L¹` rounding energy of a rational mesh is a Turán number

Continuing the NET-52 analysis of round-to-nearest (RTN) quantization, this file computes the
*total absolute* rounding error over one period of the mesh `(1/q)ℤ` — the quantity that
controls the `ℓ¹` weight perturbation of a quantized tensor whose entries are equidistributed
on the grid.  The answer is a purely combinatorial number:

`∑_{j<q} |round(j/q) − j/q| = ⌊q²/4⌋ / q`,

and `⌊q²/4⌋` is exactly the Mantel–Turán number `ex(q; K₃)`, the maximum number of edges of a
triangle-free graph on `q` vertices.  The bridge is not an accident: both count the same
optimization `max_{j} j·(q−j)` / `∑_j min(j, q−j)` over a balanced bipartition of `q`.

Main results (all proved here from scratch, so the file is self-contained):

* `four_mul_sum_min` — the exact division-free identity `4·∑_{j<q} min(j, q−j) + q % 2 = q²`.
* `sum_min_eq_turan` — hence `∑_{j<q} min(j, q−j) = ⌊q²/4⌋`, the Mantel–Turán number.
* `sawtooth_l1_period` — the real-analytic consequence: the `L¹` rounding energy of the mesh.
* `sawtooth_l1_le_quarter`, `sawtooth_l1_ge` — the mean absolute error is `1/4` of a mesh unit
  up to `O(1/q)`, i.e. *half* of the worst case `1/2` and strictly larger than the signed bias
  `1/(2q)` computed in `QuantSawtoothBias.lean`.  Absolute damage is `Θ(1)` per weight in mesh
  units, whereas the *signed* drift is `Θ(1/q)`: only compensation schemes that track signs can
  exploit the difference.
-/

open Catalog.NumberTheory.QuantTuran

open Finset




/-! ## The combinatorial identity -/

theorem Catalog.NumberTheory.QuantTuran.four_mul_sum_min(q : ℕ) :
    4 * ∑ j ∈ Finset.range q, min j (q - j) + q % 2 = q ^ 2 := by sorry
