-- Prove2me | Theorems.Thm_DepthDecay_adm_tAbove
-- name    : DepthDecay.adm_tAbove
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:47:33.503154+00:00
-- url     : https://prove2.me/theorems/c828886a-3ef1-4222-a778-23087955ad32
-- title:
--   Adm tAbove
-- statement:
--   Formal statement of `DepthDecay.adm_tAbove` from the Aether Catalog (Cryptography). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem DepthDecay.adm_tAbove{k u : ℕ} (hu : 2 ≤ u) (hue : u % 2 = 0) : Adm (tAbove k u) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/DepthDecay/UniversalNull.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/DepthDecay/UniversalNull.lean#L54

-- Thm stub generated from Cryptography/DepthDecay/UniversalNull.lean
import Mathlib
import Definitions.Def_Cryptography_DepthDecay_UniversalNull
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

open DepthDecay





/-! ### Admissibility -/

theorem DepthDecay.adm_tAbove{k u : ℕ} (hu : 2 ≤ u) (hue : u % 2 = 0) : Adm (tAbove k u) := by sorry
