-- Prove2me | Theorems.Thm_SpikeOrigin_exclusion_phase_transition
-- name    : SpikeOrigin.exclusion_phase_transition
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:01:39.482123+00:00
-- url     : https://prove2.me/theorems/2af4e0f8-30e9-4594-bc6a-22053fbca1fe
-- title:
--   Sharp phase transition of the exclusion clause.
-- statement:
--   **Sharp phase transition of the exclusion clause.**  Let `c` be a candidate normalised
--   cut-off.  If `c ≤ (√6 − 2)/4` the clause is degenerate for *every* `96`-bit modulus (no
--   full-size residue below `c`), whereas if `c > (√2 − 1)/2` it is informative for *every*
--   `96`-bit modulus (full-size residues occur below `c`).  The transition window is exactly
--   `((√6 − 2)/4, (√2 − 1)/2]`, and the experiment's `c = 1/10` sits strictly inside the
--   degenerate regime.
--
--   ```lean
--   theorem SpikeOrigin.exclusion_phase_transition{c : ℝ} :
--       (c ≤ (Real.sqrt 6 - 2) / 4 →
--         ∀ N u : ℝ, 0 < N → N < 2 ^ 96 → 0 ≤ u → u < c →
--           ((1 + 2 * u) ^ 2 - 1) * N < 2 ^ 95) ∧
--       ((Real.sqrt 2 - 1) / 2 < c →
--         ∀ N : ℝ, (2:ℝ) ^ 95 ≤ N → ∃ u : ℝ, 0 ≤ u ∧ u < c ∧ 2 ^ 95 ≤ ((1 + 2 * u) ^ 2 - 1) * N) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/SpikeOriginDegeneracy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/SpikeOriginDegeneracy.lean#L195

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










/-! ## Continuum layer: the exact crossing curve and its sharp interval -/

open Real

theorem SpikeOrigin.exclusion_phase_transition{c : ℝ} :
    (c ≤ (Real.sqrt 6 - 2) / 4 →
      ∀ N u : ℝ, 0 < N → N < 2 ^ 96 → 0 ≤ u → u < c →
        ((1 + 2 * u) ^ 2 - 1) * N < 2 ^ 95) ∧
    ((Real.sqrt 2 - 1) / 2 < c →
      ∀ N : ℝ, (2:ℝ) ^ 95 ≤ N → ∃ u : ℝ, 0 ≤ u ∧ u < c ∧ 2 ^ 95 ≤ ((1 + 2 * u) ^ 2 - 1) * N) := by sorry
