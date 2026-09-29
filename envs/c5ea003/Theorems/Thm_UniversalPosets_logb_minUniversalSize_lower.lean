-- Prove2me | Theorems.Thm_UniversalPosets_logb_minUniversalSize_lower
-- name    : UniversalPosets.logb_minUniversalSize_lower
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:07:36.970572+00:00
-- url     : https://prove2.me/theorems/b7f4e2a7-4f77-433c-bfac-bc44043efa56
-- title:
--   The counting bound in logarithmic form: `(n-1)/4 ≤ log₂ U(n)`.
-- statement:
--   The counting bound in logarithmic form: `(n-1)/4 ≤ log₂ U(n)`.
--
--   ```lean
--   theorem UniversalPosets.logb_minUniversalSize_lower(n : ℕ) (hn : 1 ≤ n) :
--       ((n : ℝ) - 1) / 4 ≤ Real.logb 2 (minUniversalSize n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/UniversalPosets/LogBounds.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/UniversalPosets/LogBounds.lean#L56

-- Thm stub generated from Cryptography/UniversalPosets/LogBounds.lean
import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_ExactSmall
import Definitions.Def_Cryptography_UniversalPosets_MinSize

/-!
# Logarithmic form of the bounds: `2^{(n-1)/4} ≤ U(n) ≤ 2^n`

The counting bound of `Bounds.lean` was stated for an even number of points
(`2 ^ m ≤ U(2m)^2`).  Here it is upgraded to **every** `n`, by splitting `n`
points into parts of sizes `⌊n/2⌋` and `⌈n/2⌉`, and then converted into the
logarithmic form in which the problem is usually phrased:

`(n-1)/4 ≤ log₂ U(n) ≤ n`.

The motivating paper ("Even smaller universal posets") proves
`log₂ U(n) ≤ (1+η)n/2` for large `n`; the exponent of `U(n)` therefore lies in
`[1/4, 1/2]`, and the two ends of that interval are exactly the two bounds
formalised in this project.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer).  The parity restriction in `2 ^ m ≤ U(2m)^2` is an
artefact of the balanced bipartite family, not of the mathematics: the unbalanced
family with parts `⌊n/2⌋`, `⌈n/2⌉` gives `2^{⌊n/2⌋⌈n/2⌉} ≤ U(n)^n`, whose
logarithm is `⌊n/2⌋⌈n/2⌉/n ≥ (n-1)/4`.

Experiment (Experimenter).  At `n = 3` the bound gives `log₂ U(3) ≥ 1/2`, i.e.
`U(3) ≥ 2`, far weaker than the exact value `5` proved in `ExactSmall.lean`; at
`n = 40` it gives `U(40) ≥ 2^{9.75} > 860`, far stronger than the linear bound
`79`.  The crossover between the two lower bounds is near `n = 20`.

Analysis (Analyst).  The two lower bounds are genuinely complementary: the
structural one is sharp for `n ≤ 3` and useless asymptotically, the counting one
is vacuous for `n ≤ 4` and dominant afterwards.  `max_lower_bound_le_logb`
records both against the same quantity.

Critique (Critic).  All statements are about `Real.logb 2 (U n)` with `U n ≥ 1`,
so no logarithm of `0` occurs; the case `n = 0` is excluded exactly where it must
be (`U 0 = 0`), and the bounds are stated with explicit hypotheses `1 ≤ n`.
-/

open UniversalPosets

open Real

theorem UniversalPosets.logb_minUniversalSize_lower(n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) - 1) / 4 ≤ Real.logb 2 (minUniversalSize n) := by sorry
