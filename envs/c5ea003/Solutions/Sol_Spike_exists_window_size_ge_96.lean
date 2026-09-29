-- Prove2me | solution 1 for Spike.exists_window_size_ge_96
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:13:34.279436+00:00
-- url     : https://prove2.me/submissions/2fe9161f-0dee-4595-a17e-a6f517a3fcaf

-- Sol generated from Probability/SpikeInclusionGeometry.lean
import Mathlib
import Definitions.Def_Probability_SpikeInclusionGeometry

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

open Spike




/-! ### Degenerate exclusion: window residues are positive -/


/-! ### The inclusion bound -/




/-! ### Bit-length consequence -/



/-! ### Sharpness of the constant and of the localisation -/




open Spike in
theorem solution:
    ∃ N j : ℕ, N < 2 ^ 96 ∧ inWindow N j ∧ 96 ≤ (residue N j).size := by
  have hsq : Nat.sqrt (2 ^ 94) = 2 ^ 47 := by
    have h : (2 : ℕ) ^ 94 = (2 ^ 47) ^ 2 := by ring
    rw [h, Nat.sqrt_eq']
  refine ⟨2 ^ 94, 3 * 2 ^ 47, by norm_num, ⟨?_, ?_⟩, ?_⟩
  · rw [hsq]; omega
  · rw [hsq]
  · have hres : residue (2 ^ 94) (3 * 2 ^ 47) = 2 ^ 97 := by
      have h : (3 * 2 ^ 47 : ℕ) ^ 2 = 2 ^ 94 + 2 ^ 97 := by ring
      simp only [residue]
      omega
    rw [hres]
    exact Nat.lt_size.mpr (by norm_num)
