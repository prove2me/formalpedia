-- Prove2me | Definitions.Def_Shared_RainbowAPRealization
-- name    : Shared_RainbowAPRealization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:13:00.621515+00:00
-- url     : https://prove2.me/theorems/de325de5-1c43-4c7a-b490-318f75db8e03
-- title:
--   Aether Catalog definitions — Shared_RainbowAPRealization
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.RainbowAPRealization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/RainbowAPRealization.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumThreshold

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

namespace RainbowAP

variable {k l m : ℕ}

/-- The word of colour patterns read off from a colouring `chi` along the `m` consecutive
`l`-term arithmetic progressions of difference `1` inside `[0, l * m)`. -/
def blockWord (l m : ℕ) (chi : ℕ → Fin k) : Fin m → (Fin l → Fin k) :=
  fun t j => chi (l * (t : ℕ) + (j : ℕ))



/-- The words of length `m` over the pattern alphabet which contain a rainbow block. -/
def rainbowWords (k l m : ℕ) : Finset (Fin m → (Fin l → Fin k)) :=
  univ.filter (fun f => ∃ t : Fin m, Function.Injective (f t))


/-- The `l`-pattern threshold with `k` colours: the least number of `l`-term progressions after
which a majority of colourings shows every one of the `k ^ l` patterns. -/
noncomputable def patternThreshold (l k : ℕ) : ℕ := spectrumThreshold (Fin l → Fin k)



end RainbowAP


