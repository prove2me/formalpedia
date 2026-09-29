-- Prove2me | Theorems.Thm_SpikeOrigin_card_lowBand
-- name    : SpikeOrigin.card_lowBand
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:00:55.002622+00:00
-- url     : https://prove2.me/theorems/7036e3b6-2f4e-4211-9365-35a948bfe603
-- title:
--   Exact population of the low band.
-- statement:
--   **Exact population of the low band.**
--
--   ```lean
--   theorem SpikeOrigin.card_lowBand(N T : ℕ) (hT : 0 < T) :
--       ((Finset.Ioc (Nat.sqrt N) (3 * Nat.sqrt N)).filter (fun j => resid N j < T)).card
--         = min (3 * Nat.sqrt N) (Nat.sqrt (N + T - 1)) - Nat.sqrt N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/SpikeOriginCounting.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/SpikeOriginCounting.lean#L61

-- Thm stub generated from Cryptography/SpikeOriginCounting.lean
import Mathlib
import Definitions.Def_Cryptography_SpikeOriginDegeneracy
/-
# Exact counting of the tiny-residue channel in a Fermat window

Companion to `Cryptography.SpikeOriginDegeneracy` and `Cryptography.SpikeOriginBands`.

The residue `v(j) = j² − N` is strictly increasing along the window `j ∈ (s, 3s]`,
`s = ⌊√N⌋`.  Consequently *every* bit-length band is an interval of positions, and the
"exclude `v < T`" clause is, for a **fixed** modulus, literally a positional cut at
`j ≤ ⌊√(N + T − 1)⌋`.  We compute the excluded population exactly
(`card_lowBand`) and show for `96`-bit moduli that the excluded left-edge interval has
width at least `0.22 · s`, i.e. it strictly contains the whole first decile (width `0.2 s`)
with a margin of at least `0.02 · s` positions.

Combined with `SpikeOriginBands.midRegime_not_universal` — where the cut position moves with
`N` — this is the precise form of "the spike is not one object": *within* a modulus the
`bitlen v` band and the position are the same stratification, *across* moduli they are not.

The tiny channel reaches all the way down to `v ≤ 2√N + 1` (`resid_left_end_le`), i.e.
about half the bit-length of `N`, which is the arithmetic mechanism behind the inclusion
artifact.
-/

open SpikeOrigin

/-! ## Monotonicity: bands are positional intervals -/

theorem SpikeOrigin.card_lowBand(N T : ℕ) (hT : 0 < T) :
    ((Finset.Ioc (Nat.sqrt N) (3 * Nat.sqrt N)).filter (fun j => resid N j < T)).card
      = min (3 * Nat.sqrt N) (Nat.sqrt (N + T - 1)) - Nat.sqrt N := by sorry
