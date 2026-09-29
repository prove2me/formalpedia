-- Prove2me | Definitions.Def_Probability_SpikeInclusionGeometry
-- name    : Probability_SpikeInclusionGeometry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:36:28.748261+00:00
-- url     : https://prove2.me/theorems/750b7649-c305-4a93-929a-c134e49fc97b
-- title:
--   Aether Catalog definitions — Probability_SpikeInclusionGeometry
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.SpikeInclusionGeometry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/SpikeInclusionGeometry.lean by skeleton subtraction
import Mathlib

/-!
# Window geometry forces tiny `v` at the left edge (the inclusion artifact)

This file formalises the *mechanical forcing* half of the round-85 resolution of
the "left-edge spike".  The empirical situation is:

* a sieve-type search stores, for each modulus `N`, the residues
  `v N j = j^2 - N` at positions `j` running over the window
  `W N = [isqrt N + 1, 3 * isqrt N]`;
* the *first decile* `D1` of that window is the leading tenth of it, i.e. the
  positions `j` with `10 * (j - isqrt N) ≤ 2 * isqrt N`, equivalently
  `5 * j ≤ 6 * isqrt N`;
* the empirical `D1` hit mass split by `bitlen v` was
  `< 80 : 0`, `80–89 : 85`, `90–95 : 1469`, `≥ 96 : 0`.

The observation that *no* `D1` hit can have `bitlen v ≥ 96` is not statistics:
it is a theorem of exact integer arithmetic about the window.  We prove it here
in the sharp form

`25 * v N j ≤ 11 * (isqrt N)^2`  for every first-decile position,

i.e. `v ≤ 0.44 * s^2 ≤ 0.44 * N`, together with

* the general scale-carrying version with an arbitrary rational edge fraction
  `p/q` (`Spike.residue_le_of_edge_frac`), whose constant `2pq + p^2` degrades
  gracefully as the window prefix grows;
* the bit-length corollary `Spike.size_residue_lt_96` : for `N < 2 ^ 96` every
  first-decile residue satisfies `bitlen v < 96`;
* its contrapositive `Spike.not_first_decile_of_size_ge_96` : any stored hit
  with `bitlen v ≥ 96` is *outside* the first decile — the exclusion is total,
  not statistical;
* sharpness `Spike.residue_edge_sharp` : the constant `11/25` is attained, and
  `Spike.exists_window_size_ge_96` : positions further into the same window do
  carry `bitlen v ≥ 96`, so the bound really is a property of the edge and not
  of the window as a whole;
* the degenerate-exclusion clause `Spike.residue_pos` : residues at window
  positions are strictly positive, so `bitlen` is well defined on them.

Consequence for the statistics: the first decile is a *pure tiny-`v` stratum*.
Any comparison of the first decile against the whole-window `v` distribution is
therefore confounded with magnitude by construction; see
`Catalog/Probability/SpikeBandComposition.lean` for the composition accounting
and `Catalog/Probability/SpikeStratifiedEvidence.lean` for the model-selection
consequence.
-/

namespace Spike

/-- The residue stored at window position `j` for modulus `N`. -/
def residue (N j : ℕ) : ℕ := j ^ 2 - N

/-- The search window: `j ∈ [isqrt N + 1, 3 * isqrt N]`. -/
def inWindow (N j : ℕ) : Prop := Nat.sqrt N + 1 ≤ j ∧ j ≤ 3 * Nat.sqrt N

/-- The first decile of the window: the leading tenth of the `2 * isqrt N`
positions, i.e. `10 * (j - isqrt N) ≤ 2 * isqrt N`. -/
def inFirstDecile (N j : ℕ) : Prop := inWindow N j ∧ 5 * j ≤ 6 * Nat.sqrt N

/-! ### Degenerate exclusion: window residues are positive -/


/-! ### The inclusion bound -/




/-! ### Bit-length consequence -/



/-! ### Sharpness of the constant and of the localisation -/



end Spike


