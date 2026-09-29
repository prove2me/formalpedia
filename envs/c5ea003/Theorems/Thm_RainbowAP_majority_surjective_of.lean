-- Prove2me | Theorems.Thm_RainbowAP_majority_surjective_of
-- name    : RainbowAP.majority_surjective_of
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:49:01.875794+00:00
-- url     : https://prove2.me/theorems/ce8be679-e2df-437e-9b41-d854187ecde2
-- title:
--   Union-bound criterion.
-- statement:
--   **Union-bound criterion.** If `2 N (N-1)^m < N^m` then a strict majority of the words of
--   length `m` are surjective.
--
--   ```lean
--   theorem RainbowAP.majority_surjective_of(m : ℕ)
--       (h : 2 * Fintype.card α * (Fintype.card α - 1) ^ m < Fintype.card α ^ m) :
--       2 * nonSurjCount α m < Fintype.card α ^ m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPSpectrumThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPSpectrumThreshold.lean#L73

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

theorem RainbowAP.majority_surjective_of(m : ℕ)
    (h : 2 * Fintype.card α * (Fintype.card α - 1) ^ m < Fintype.card α ^ m) :
    2 * nonSurjCount α m < Fintype.card α ^ m := by sorry
