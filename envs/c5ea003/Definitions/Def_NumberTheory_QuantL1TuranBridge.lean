-- Prove2me | Definitions.Def_NumberTheory_QuantL1TuranBridge
-- name    : NumberTheory_QuantL1TuranBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:13:15.430616+00:00
-- url     : https://prove2.me/theorems/32dd45e3-f52b-487f-a838-57d747671e5d
-- title:
--   Aether Catalog definitions — NumberTheory_QuantL1TuranBridge
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.QuantL1TuranBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/QuantL1TuranBridge.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.NumberTheory.QuantTuran

open Finset

/-- The signed round-to-nearest error at unit mesh. -/
noncomputable def sawtooth (x : ℝ) : ℝ := (round x : ℝ) - x



/-! ## The combinatorial identity -/









end Catalog.NumberTheory.QuantTuran


