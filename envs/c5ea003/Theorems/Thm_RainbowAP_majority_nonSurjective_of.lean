-- Prove2me | Theorems.Thm_RainbowAP_majority_nonSurjective_of
-- name    : RainbowAP.majority_nonSurjective_of
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:48:50.016973+00:00
-- url     : https://prove2.me/theorems/a1b48f3c-9760-4c1a-84be-a1d71db18f02
-- title:
--   Second-moment criterion.
-- statement:
--   **Second-moment criterion.** If `N^m < (N+1)(N-1)^m` then a strict majority of the words of
--   length `m` are *not* surjective.
--
--   ```lean
--   theorem RainbowAP.majority_nonSurjective_of(m : ℕ) (hN : 2 ≤ Fintype.card α)
--       (h : Fintype.card α ^ m < (Fintype.card α + 1) * (Fintype.card α - 1) ^ m) :
--       Fintype.card α ^ m < 2 * nonSurjCount α m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPSpectrumThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPSpectrumThreshold.lean#L84

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

theorem RainbowAP.majority_nonSurjective_of(m : ℕ) (hN : 2 ≤ Fintype.card α)
    (h : Fintype.card α ^ m < (Fintype.card α + 1) * (Fintype.card α - 1) ^ m) :
    Fintype.card α ^ m < 2 * nonSurjCount α m := by sorry
