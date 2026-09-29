-- Prove2me | Definitions.Def_Cryptography_SpikeOriginDegeneracy
-- name    : Cryptography_SpikeOriginDegeneracy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:23:21.615065+00:00
-- url     : https://prove2.me/theorems/138f0909-9a58-4f0d-b8fb-432f4aa32e92
-- title:
--   Aether Catalog definitions — Cryptography_SpikeOriginDegeneracy
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.SpikeOriginDegeneracy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/SpikeOriginDegeneracy.lean by skeleton subtraction
import Mathlib
/-
# Spike-origin degeneracy: the left-edge decile of a Fermat window carries only tiny residues

Setting (exp 589 / paper 239).  For a modulus `N` one scans trial points `j` in the
Fermat-style window `j ∈ (s, 3s]`, `s = ⌊√N⌋`, and records the residue `v = j² − N`.
Positions are normalised to `u = (j − s) / (2s) ∈ (0, 1]`.  The empirical study reports a
left-edge spike concentrated in the *first decile* `D1 = {u ≲ 1/10}` and asks whether the
"exclude `v < 2⁹⁵`" clause can discriminate anything there.

This file proves, by exact arithmetic, that the clause is **degenerate**: every `D1` point
of a `96`-bit modulus has `v < 2⁹⁵`, i.e. `bitlen v ≤ 95`, so the exclusion removes
*100 %* of the `D1` mass by geometry alone.  The mechanism is scale free
(`resid_lt_of_firstDecile_scalefree`: `v < 0.45 · N`) and it is **sharp**: past position
`u ≈ 0.21` the residue is provably full size, and in the continuum the exact transition
point is the crossing curve `u₀(N) = (√(1 + 2⁹⁵/N) − 1)/2`, which is pinned to the interval
`((√6 − 2)/4, (√2 − 1)/2] ⊂ (0.1123, 0.2072]`.  In particular the decile boundary `1/10`
lies *strictly below* the smallest possible crossing `(√6 − 2)/4 = 0.11237…`, which is the
structural reason for the degeneracy — and it also explains the reported kept-support left
edge `u ≈ 0.114`.
-/

namespace SpikeOrigin

/-! ## Discrete layer: window, residue, first decile -/

/-- The residue attached to a trial point `j` for the modulus `N`, i.e. `j² − N`
(truncated subtraction; in all uses below `j > ⌊√N⌋`, so `j² > N`). -/
def resid (N j : ℕ) : ℕ := j ^ 2 - N


/-- The first decile of the window, in the (slack) form used by the experiment:
`δ = j − s` satisfies `5δ < s + 5`, i.e. `δ < 0.2 s + 1`.  Since the window has width
`2s`, this is the normalised position range `u = δ/(2s) ≲ 1/10`. -/
def FirstDecile (N j : ℕ) : Prop := Nat.sqrt N < j ∧ 5 * (j - Nat.sqrt N) < Nat.sqrt N + 5







/-! ## Continuum layer: the exact crossing curve and its sharp interval -/

open Real

/-- Normalised crossing position: the value of `u = (j − s)/(2s)` at which the residue
`((1 + 2u)² − 1) · N` first reaches the full-size threshold `2⁹⁵`. -/
noncomputable def crossingPos (N : ℝ) : ℝ := (Real.sqrt (1 + 2 ^ 95 / N) - 1) / 2






end SpikeOrigin


