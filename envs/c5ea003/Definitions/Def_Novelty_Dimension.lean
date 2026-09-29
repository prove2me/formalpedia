-- Prove2me | Definitions.Def_Novelty_Dimension
-- name    : Novelty_Dimension
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:14:00.131446+00:00
-- url     : https://prove2.me/theorems/41440350-8b0c-4790-baf1-3d1eb9e84c72
-- title:
--   Aether Catalog definitions — Novelty_Dimension
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Dimension`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Dimension.lean by skeleton subtraction
import Mathlib

/-!
# Proof Space IV: The dimension of proof space and the length distribution

The exponential growth rate of proof space,

  `dim = lim_{n→∞} log (tot n) / n`,

plays the role of a Hausdorff / box-counting dimension: it measures how the
"volume" of proof space scales with resolution `n`.  For an alphabet of size `k`
this dimension equals `log k`, the topological entropy of the full shift.

We also introduce the induced *length distribution* on statements: weighting each
length `n` by the geometric factor `(k-1)/k^{n+1}` gives a genuine probability
distribution (`lengthDist_tsum`).  Its geometric tail `∝ k^{-n}` is, in the
length variable, exactly the power law predicted for the distribution of theorem
lengths, with rate controlled by the dimension `log k`.
-/

namespace ProofSpace

open Filter Topology Real



/-- The length distribution: length `n` gets weight `(k-1)/k^{n+1}`. -/
noncomputable def lengthDist (k : ℝ) (n : ℕ) : ℝ := (k - 1) / k ^ (n + 1)



end ProofSpace


