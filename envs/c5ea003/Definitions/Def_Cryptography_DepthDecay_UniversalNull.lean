-- Prove2me | Definitions.Def_Cryptography_DepthDecay_UniversalNull
-- name    : Cryptography_DepthDecay_UniversalNull
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:12:50.967267+00:00
-- url     : https://prove2.me/theorems/b3a9279a-d815-4f65-a41a-4cd7aa6d0d4b
-- title:
--   Aether Catalog definitions — Cryptography_DepthDecay_UniversalNull
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.DepthDecay.UniversalNull`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/DepthDecay/UniversalNull.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_DepthDecay_WindowSensor

/-!
# Every rational-scale magnitude sensor is null beyond the first inversion

`Cryptography.DepthDecay.NullBeyondInversion` defeats the dyadic window sensor
`⌊2^W · m/n⌋`.  One might hope that the failure is an artefact of *binary*
truncation — after all, the offending boundary `7/3` is invisible to base `2` but
plainly visible to base `3`.  This file shows that no change of scale helps.

For arbitrary positive integers `a, b` consider the sensor

  `gprobe a b (m,n) = ⌊(a/b) · (m/n)⌋`,

i.e. any monotone rational rescaling of the magnitude followed by truncation
(`gprobe (2^W) 1 = probe W`).  We prove: **for every scale `a/b` and every depth
`k` the sensor confuses two admissible states which agree on the whole prefix
`C^k B` and differ at depth `k+1`.**

The mechanism is different from — and stronger than — the `7/3` straddle.  Here
the boundary `5/2 + 2k` is *attained* by the admissible state `(4k+5, 2)`, whose
inversion lands exactly on the root; states just above it invert to ratios below
`2` and take the letter `A`.  Since `⌊·⌋` is right-continuous, no truncation
sensor of any scale can separate an attained boundary from its right neighbours.
-/

namespace DepthDecay

/-- A magnitude sensor of arbitrary rational scale: `⌊(a/b)·(m/n)⌋`. -/
def gprobe (a b : ℕ) (s : ℕ × ℕ) : ℕ := a * s.1 / (b * s.2)


/-- The boundary state: ratio exactly `5/2 + 2k`, whose inversion hits the root. -/
def tBoundary (k : ℕ) : ℕ × ℕ := (4 * k + 5, 2)

/-- A state just above the boundary, at resolution `1/(2u)`. -/
def tAbove (k u : ℕ) : ℕ × ℕ := ((4 * k + 5) * u + 1, 2 * u)

/-! ### Admissibility -/



/-! ### Descent letters of the two states -/







/-! ### The sensor cannot separate them -/


/-! ### Main theorem -/



end DepthDecay


