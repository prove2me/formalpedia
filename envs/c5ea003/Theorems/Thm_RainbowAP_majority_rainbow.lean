-- Prove2me | Theorems.Thm_RainbowAP_majority_rainbow
-- name    : RainbowAP.majority_rainbow
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:49:59.716984+00:00
-- url     : https://prove2.me/theorems/2befe2fc-ec82-4180-9813-40b0f76ac1e3
-- title:
--   Above the union-bound threshold, a strict majority of all pattern words already contains a
-- statement:
--   Above the union-bound threshold, a strict majority of all pattern words already contains a
--   rainbow block, hence encodes a colouring with a rainbow `l`-term progression.
--
--   ```lean
--   theorem RainbowAP.majority_rainbow(hl : l ≤ k)
--       (h : 2 * Fintype.card (Fin l → Fin k) * (Fintype.card (Fin l → Fin k) - 1) ^ m
--           < Fintype.card (Fin l → Fin k) ^ m) :
--       Fintype.card (Fin l → Fin k) ^ m < 2 * (rainbowWords k l m).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPRealization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPRealization.lean#L71

-- Thm stub generated from Shared/RainbowAPRealization.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPRealization

/-!
# From full spectra to genuine rainbow arithmetic progressions

The threshold studied in `Shared.RainbowAPSpectrumThreshold` is about words over an alphabet.
Here we give that alphabet its combinatorial meaning: the alphabet `Fin l → Fin k` is the set of
*colour patterns* of an `l`-term arithmetic progression coloured with `k` colours, and a word of
length `m` over it is exactly the restriction of a `k`-colouring of the interval `[0, l m)` to the
`m` consecutive `l`-term progressions of common difference `1`.

Main results.

* `RainbowAP.exists_rainbow_block` : a full-spectrum word contains an injective (rainbow) pattern
  as soon as `l ≤ k`.
* `RainbowAP.exists_rainbow_AP` : consequently, a `k`-colouring of `ℕ` whose block word on
  `[0, l m)` has full spectrum contains a genuine rainbow `l`-term arithmetic progression inside
  `[0, l m)`.
* `RainbowAP.majority_rainbow` : above the union-bound threshold, a strict majority of all
  patterns of length `m` already contain a rainbow progression.
* `RainbowAP.patternThreshold_bounds` : the `l`-pattern threshold is
  `Θ(k^l log(k^l))`; for `l = 2` this is the `Θ(k² log k)` regime of `Shared.RainbowAPPairThreshold`.
-/

open Finset

open RainbowAP

variable {k l m : ℕ}

theorem RainbowAP.majority_rainbow(hl : l ≤ k)
    (h : 2 * Fintype.card (Fin l → Fin k) * (Fintype.card (Fin l → Fin k) - 1) ^ m
        < Fintype.card (Fin l → Fin k) ^ m) :
    Fintype.card (Fin l → Fin k) ^ m < 2 * (rainbowWords k l m).card := by sorry
