-- Prove2me | Definitions.Def_Algebra_ScanSchemeDecoding_Spectrum
-- name    : Algebra_ScanSchemeDecoding_Spectrum
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T10:13:24.683788+00:00
-- url     : https://prove2.me/theorems/e3714b16-4bfc-4491-899e-355b516813a4
-- title:
--   Aether Catalog definitions — Algebra_ScanSchemeDecoding_Spectrum
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.ScanSchemeDecoding.Spectrum`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/ScanSchemeDecoding/Spectrum.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core

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

namespace ScanSchemeDecoding

open Finset



namespace ScanScheme

variable {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [DecidableEq β]
variable (S : ScanScheme α β)


end ScanScheme

/-- The degenerate scheme that puts every key in a single bucket. -/
def constScheme (N : ℕ) {m : ℕ} (b₀ : Fin m) : ScanScheme (Fin N) (Fin m) := ⟨fun _ => b₀⟩




end ScanSchemeDecoding


