-- Prove2me | Theorems.Thm_ScanSchemeDecoding_ScanScheme_mean_decodeCost_ge_inv_two_mul
-- name    : ScanSchemeDecoding.ScanScheme.mean_decodeCost_ge_inv_two_mul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:58:36.595411+00:00
-- url     : https://prove2.me/theorems/6e74b16b-9fcf-413c-8f15-ff5d8a11289e
-- title:
--   The `ε`-compression barrier.
-- statement:
--   **The `ε`-compression barrier.**  If the index is compressed to `m ≤ ε · N` buckets
--   then the mean decoding cost is at least `1 / (2ε)`: buying a factor `ε` of space costs a
--   factor `1/ε` of time, with the exact constant `1/2`.
--
--   ```lean
--   theorem ScanSchemeDecoding.ScanScheme.mean_decodeCost_ge_inv_two_mul(eps : ℝ) (heps : 0 < eps)
--       (hα : 0 < Fintype.card α) (hβ : 0 < Fintype.card β)
--       (hcomp : (Fintype.card β : ℝ) ≤ eps * (Fintype.card α : ℝ)) :
--       1 / (2 * eps) ≤ (∑ x, S.decodeCost x : ℝ) / (Fintype.card α : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ScanSchemeDecoding/Epsilon.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ScanSchemeDecoding/Epsilon.lean#L73

-- Thm stub generated from Algebra/ScanSchemeDecoding/Epsilon.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core

/-!
# The `ε`-compression barrier for scan indices

The exact pigeonhole optimum of `Algebra.ScanSchemeDecoding.Triangle` is stated with the
*floor* `⌊N/m⌋`.  Here we sharpen it to a statement with genuine (real) division, which
is the form in which a space/time trade-off is usually quoted:

  `N * (N + m) ≤ 2 * m * triangleOpt N m`  (`triangleOpt_mul_ge`, an exact `ℕ` statement),

and deduce the analytic corollaries

* `mean_decodeCost_ge` — the mean decoding cost of any scan scheme is at least
  `(N/m + 1)/2`;
* `mean_decodeCost_ge_inv_two_mul` — the **`ε`-compression barrier**: a scheme whose
  index uses only `m ≤ ε · N` buckets has mean decoding cost at least `1/(2ε)`.

Both are sharp: for `m ∣ N` the residue scheme of `Algebra.ScanSchemeDecoding.Optimum`
meets the first bound with equality (`mean_decodeCost_modScheme_eq` for `m ∣ N`).
-/

open ScanSchemeDecoding

open Finset


open ScanScheme

variable {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [DecidableEq β]
variable (S : ScanScheme α β)

theorem ScanSchemeDecoding.ScanScheme.mean_decodeCost_ge_inv_two_mul(eps : ℝ) (heps : 0 < eps)
    (hα : 0 < Fintype.card α) (hβ : 0 < Fintype.card β)
    (hcomp : (Fintype.card β : ℝ) ≤ eps * (Fintype.card α : ℝ)) :
    1 / (2 * eps) ≤ (∑ x, S.decodeCost x : ℝ) / (Fintype.card α : ℝ) := by sorry
