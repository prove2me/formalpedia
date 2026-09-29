-- Prove2me | Theorems.Thm_SpikeOrigin_resid_ge_two_pow_95_of_far
-- name    : SpikeOrigin.resid_ge_two_pow_95_of_far
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:02:23.614506+00:00
-- url     : https://prove2.me/theorems/28dab641-3f4d-4d94-bc69-6436cd45a300
-- title:
--   Non-vacuity / sharpness of the discrete threshold.
-- statement:
--   **Non-vacuity / sharpness of the discrete threshold.**  Past normalised position
--   `u = 0.21` (i.e. `100 j ≥ 142 s`) the residue of a `96`-bit modulus is provably *full size*,
--   `v ≥ 2⁹⁵`.  So the exclusion clause is not globally trivial: it is exactly the first decile
--   that it annihilates.
--
--   ```lean
--   theorem SpikeOrigin.resid_ge_two_pow_95_of_far{N j : ℕ} (hlo : 2 ^ 95 ≤ N) (hhi : N < 2 ^ 96)
--       (hfar : 142 * Nat.sqrt N ≤ 100 * j) : 2 ^ 95 ≤ resid N j := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/SpikeOriginDegeneracy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/SpikeOriginDegeneracy.lean#L95

-- Thm stub generated from Cryptography/SpikeOriginDegeneracy.lean
import Mathlib
import Definitions.Def_Cryptography_SpikeOriginDegeneracy
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

open SpikeOrigin

/-! ## Discrete layer: window, residue, first decile -/

theorem SpikeOrigin.resid_ge_two_pow_95_of_far{N j : ℕ} (hlo : 2 ^ 95 ≤ N) (hhi : N < 2 ^ 96)
    (hfar : 142 * Nat.sqrt N ≤ 100 * j) : 2 ^ 95 ≤ resid N j := by sorry
