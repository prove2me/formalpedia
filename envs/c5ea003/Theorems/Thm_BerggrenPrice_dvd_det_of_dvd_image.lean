-- Prove2me | Theorems.Thm_BerggrenPrice_dvd_det_of_dvd_image
-- name    : BerggrenPrice.dvd_det_of_dvd_image
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:27:00.88143+00:00
-- url     : https://prove2.me/theorems/347a738c-1838-4b7a-aca7-fa4ae2756233
-- title:
--   A common divisor of the image of a coprime pair under an integer matrix divides the
-- statement:
--   A common divisor of the image of a coprime pair under an integer matrix divides the
--   determinant of that matrix.
--
--   ```lean
--   theorem BerggrenPrice.dvd_det_of_dvd_image{a b c d x y k : ℤ} (hxy : IsCoprime x y)
--       (h1 : k ∣ a * x + b * y) (h2 : k ∣ c * x + d * y) : k ∣ a * d - b * c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/BerggrenPriceInterlock/Classification.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/BerggrenPriceInterlock/Classification.lean#L21

-- Thm stub generated from Algebra/BerggrenPriceInterlock/Classification.lean
import Mathlib
import Definitions.Def_Algebra_BerggrenPriceInterlock_Trees

/-!
# Berggren–Price interlock, Part VII: what a tree generator can look like

Why is determinant `±2` allowed at all?  Two structural facts explain the interlock:

* `dvd_det_of_dvd_image` — a common divisor of the image of a coprime pair divides the
  determinant.  So a generator of determinant `±1` preserves coprimality for free, while
  a generator of determinant `±2` preserves it only because the parity condition forces
  the gcd to be odd.  This is exactly the gap Price's tree lives in.
* `node_map_parity` — any integer linear map sending nodes to nodes has *odd column
  sums* `a + c` and `b + d`.  Both generator triples satisfy this, and it is what rules
  out the naive "halving" maps such as `(m,n) ↦ (2m−n, n)`.

Together these are the two constraints that any classification of ternary Pythagorean
trees must start from (see `FUTURE_DIRECTIONS.md`, conjecture C4).
-/

open BerggrenPrice

theorem BerggrenPrice.dvd_det_of_dvd_image{a b c d x y k : ℤ} (hxy : IsCoprime x y)
    (h1 : k ∣ a * x + b * y) (h2 : k ∣ c * x + d * y) : k ∣ a * d - b * c := by sorry
