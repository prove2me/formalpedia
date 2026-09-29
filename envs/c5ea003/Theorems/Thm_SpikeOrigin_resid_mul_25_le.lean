-- Prove2me | Theorems.Thm_SpikeOrigin_resid_mul_25_le
-- name    : SpikeOrigin.resid_mul_25_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:01:49.947883+00:00
-- url     : https://prove2.me/theorems/0f959b67-2c7e-4a66-89b3-81c8b1eb2bad
-- title:
--   Core arithmetic bound.
-- statement:
--   **Core arithmetic bound.**  On the first decile the residue obeys
--   `25 v ≤ 11 N + 48 √N + 16`; the leading constant `11/25 = 0.44` is exactly the
--   `(1 + 0.2)² − 1` of the informal computation.
--
--   ```lean
--   theorem SpikeOrigin.resid_mul_25_le{N j : ℕ} (h : FirstDecile N j) :
--       25 * resid N j ≤ 11 * N + 48 * Nat.sqrt N + 16 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/SpikeOriginDegeneracy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/SpikeOriginDegeneracy.lean#L42

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

theorem SpikeOrigin.resid_mul_25_le{N j : ℕ} (h : FirstDecile N j) :
    25 * resid N j ≤ 11 * N + 48 * Nat.sqrt N + 16 := by sorry
