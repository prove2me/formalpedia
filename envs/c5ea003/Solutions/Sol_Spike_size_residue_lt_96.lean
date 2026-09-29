-- Prove2me | solution 1 for Spike.size_residue_lt_96
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:16:17.259897+00:00
-- url     : https://prove2.me/submissions/119d39f2-2a33-457e-bc5b-64676d028cbf

-- Sol generated from Probability/SpikeInclusionGeometry.lean
import Mathlib
import Definitions.Def_Probability_SpikeInclusionGeometry
import Theorems.Thm_Spike_residue_le_of_edge_frac

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


/-- **First-decile inclusion bound**: `25 * v ≤ 11 * (isqrt N)^2`, i.e.
`v ≤ 0.44 * s^2`.  This is the `p = 1, q = 5` instance. -/
theorem residue_le_of_first_decile {N j : ℕ} (h : inFirstDecile N j) :
    25 * residue N j ≤ 11 * Nat.sqrt N ^ 2 := by
  have := residue_le_of_edge_frac (N := N) (j := j) (p := 1) (q := 5)
    (by simpa using h.2)
  norm_num at this
  simpa using this

/-- Since `s^2 ≤ N`, the first-decile bound also reads `v ≤ 0.44 * N`. -/
theorem residue_le_of_first_decile' {N j : ℕ} (h : inFirstDecile N j) :
    25 * residue N j ≤ 11 * N :=
  le_trans (residue_le_of_first_decile h)
    (Nat.mul_le_mul_left _ (Nat.sqrt_le' N))

/-! ### Bit-length consequence -/



/-! ### Sharpness of the constant and of the localisation -/




open Spike in
theorem solution{N j : ℕ} (hN : N < 2 ^ 96) (h : inFirstDecile N j) :
    (residue N j).size < 96 := by
  have h25 : 25 * residue N j ≤ 11 * N := residue_le_of_first_decile' h
  have hlt : residue N j < 2 ^ 95 := by
    by_contra hcon
    push_neg at hcon
    have h1 : 25 * 2 ^ 95 ≤ 25 * residue N j := Nat.mul_le_mul le_rfl hcon
    omega
  have : (residue N j).size ≤ 95 := Nat.size_le.mpr hlt
  omega
