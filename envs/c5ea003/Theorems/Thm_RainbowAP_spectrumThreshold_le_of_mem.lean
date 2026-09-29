-- Prove2me | Theorems.Thm_RainbowAP_spectrumThreshold_le_of_mem
-- name    : RainbowAP.spectrumThreshold_le_of_mem
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:26:25.78198+00:00
-- url     : https://prove2.me/theorems/fa4afee0-8bc6-42bc-901c-2e84889c8f12
-- title:
--   Spectrum threshold le of mem
-- statement:
--   Formal statement of `RainbowAP.spectrumThreshold_le_of_mem` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RainbowAP.spectrumThreshold_le_of_mem{m : ℕ}
--       (h : 2 * nonSurjCount α m < Fintype.card α ^ m) :
--       spectrumThreshold α ≤ m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPSpectrumThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPSpectrumThreshold.lean#L144

-- Thm stub generated from Shared/RainbowAPSpectrumThreshold.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumMoments
import Definitions.Def_Shared_RainbowAPSpectrumThreshold

/-!
# The full-spectrum (coupon-collector) threshold for words over a finite alphabet

For a finite alphabet `α` with `N = |α|` letters, a word `f : Fin m → α` has *full spectrum*
if it is surjective, i.e. every letter of `α` occurs.  We study the counting threshold

  `spectrumThreshold α = least m such that a strict majority of the `N ^ m` words of length `m`
   have full spectrum`.

The two criteria proved here are purely arithmetic and come from the first and second moment
identities of `Shared.RainbowAPSpectrumMoments`:

* if `2 * N * (N-1)^m < N^m` then the majority is surjective (union bound / first moment);
* if `N^m < (N+1) * (N-1)^m` then the majority is **not** surjective
  (Cauchy–Schwarz / second moment).

Both criteria are sharp up to the additive constants inside the logarithm, which is what makes
the resulting threshold asymptotically `N log N`.
-/

open Finset

open RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem RainbowAP.spectrumThreshold_le_of_mem{m : ℕ}
    (h : 2 * nonSurjCount α m < Fintype.card α ^ m) :
    spectrumThreshold α ≤ m := by sorry
