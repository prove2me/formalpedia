-- Prove2me | Theorems.Thm_RainbowAP_exists_rainbow_AP
-- name    : RainbowAP.exists_rainbow_AP
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:49:46.016982+00:00
-- url     : https://prove2.me/theorems/8cb4be38-71d1-409b-8b2a-6681e2087c16
-- title:
--   A colouring whose block word has full spectrum contains a genuine rainbow `l`-term
-- statement:
--   A colouring whose block word has full spectrum contains a genuine rainbow `l`-term
--   arithmetic progression (of common difference `1`) inside `[0, l * m)`.
--
--   ```lean
--   theorem RainbowAP.exists_rainbow_AP(hl : l ≤ k) (hl1 : 1 ≤ l) (chi : ℕ → Fin k)
--       (hf : Function.Surjective (blockWord l m chi)) :
--       ∃ a d : ℕ, 0 < d ∧ a + (l - 1) * d < l * m ∧
--         Function.Injective (fun j : Fin l => chi (a + (j : ℕ) * d)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPRealization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPRealization.lean#L49

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

theorem RainbowAP.exists_rainbow_AP(hl : l ≤ k) (hl1 : 1 ≤ l) (chi : ℕ → Fin k)
    (hf : Function.Surjective (blockWord l m chi)) :
    ∃ a d : ℕ, 0 < d ∧ a + (l - 1) * d < l * m ∧
      Function.Injective (fun j : Fin l => chi (a + (j : ℕ) * d)) := by sorry
