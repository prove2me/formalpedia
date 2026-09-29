-- Prove2me | Theorems.Thm_ScanSchemeDecoding_constScheme_decodeCost
-- name    : ScanSchemeDecoding.constScheme_decodeCost
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:58:39.337986+00:00
-- url     : https://prove2.me/theorems/4107c91d-33f3-4537-9e98-8ade23279409
-- title:
--   The one-bucket scheme costs exactly `triangle N`.
-- statement:
--   The one-bucket scheme costs exactly `triangle N`.
--
--   ```lean
--   theorem ScanSchemeDecoding.constScheme_decodeCost(N : ℕ) {m : ℕ} (b₀ : Fin m) :
--       ∑ x, (constScheme N b₀).decodeCost x = triangle N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ScanSchemeDecoding/Spectrum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ScanSchemeDecoding/Spectrum.lean#L57

-- Thm stub generated from Algebra/ScanSchemeDecoding/Spectrum.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
import Definitions.Def_Algebra_ScanSchemeDecoding_Spectrum
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle

/-!
# The cost spectrum of scan schemes

The exact optimum pins down the *bottom* of the achievable total-cost spectrum.  Here we
pin down the *top*: the triangular number `triangle N` of the whole key set, attained by
the degenerate one-bucket scheme.  The mechanism is the exact opposite of convexity used
for the optimum, namely superadditivity `triangle a + triangle b ≤ triangle (a + b)`.

## Main results

* `ScanSchemeDecoding.triangle_add_le` — superadditivity of the triangular cost.
* `ScanSchemeDecoding.sum_triangle_le` — a scan scheme never costs more than a single
  linear scan of all keys.
* `ScanSchemeDecoding.scan_maximum` — `triangle N` is the greatest achievable cost.
* `ScanSchemeDecoding.scan_cost_spectrum` — every scan scheme on `N` keys with `m > 0`
  buckets has total cost in the closed interval `[triangleOpt N m, triangle N]`, and both
  endpoints are realised.
-/

open ScanSchemeDecoding

open Finset



open ScanScheme

variable {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [DecidableEq β]
variable (S : ScanScheme α β)

theorem ScanSchemeDecoding.constScheme_decodeCost(N : ℕ) {m : ℕ} (b₀ : Fin m) :
    ∑ x, (constScheme N b₀).decodeCost x = triangle N := by sorry
