-- Prove2me | Theorems.Thm_ScanSchemeDecoding_triangleOpt_mul_ge
-- name    : ScanSchemeDecoding.triangleOpt_mul_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:58:27.234769+00:00
-- url     : https://prove2.me/theorems/19b7189d-9f47-4a68-9c07-d0819a2a497d
-- title:
--   Exact, division-free form of the averaged optimum.
-- statement:
--   Exact, division-free form of the averaged optimum.
--
--   ```lean
--   theorem ScanSchemeDecoding.triangleOpt_mul_ge{m : ℕ} (hm : 0 < m) (N : ℕ) :
--       N * (N + m) ≤ 2 * m * triangleOpt N m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ScanSchemeDecoding/Epsilon.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ScanSchemeDecoding/Epsilon.lean#L26

-- Thm stub generated from Algebra/ScanSchemeDecoding/Epsilon.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle

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

theorem ScanSchemeDecoding.triangleOpt_mul_ge{m : ℕ} (hm : 0 < m) (N : ℕ) :
    N * (N + m) ≤ 2 * m * triangleOpt N m := by sorry
