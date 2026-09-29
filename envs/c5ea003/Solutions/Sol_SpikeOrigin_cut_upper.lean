-- Prove2me | solution 1 for SpikeOrigin.cut_upper
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:35:59.785472+00:00
-- url     : https://prove2.me/submissions/0b5c0b49-39cb-4b28-ac08-faa3e183664f

-- Sol generated from Cryptography/SpikeOriginCounting.lean
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






/-! ## How small the tiny channel gets -/


/-! ## The excluded interval strictly contains the first decile (96-bit case) -/


variable {N : ℕ}

private lemma sqrt_sq_le (N : ℕ) : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N






/-! ## Monotone law for the continuum crossing position -/



open SpikeOrigin in
theorem solution(hlo : 2 ^ 95 ≤ N) (hhi : N < 2 ^ 96) :
    100 * Nat.sqrt (N + 2 ^ 95 - 1) ≤ 142 * Nat.sqrt N := by
  set s := Nat.sqrt N with hs
  have h1 : s * s ≤ N := sqrt_sq_le N
  have hup : N < (s + 1) * (s + 1) := by
    have := Nat.lt_succ_sqrt' N
    simpa [hs, pow_two] using this
  have hslarge : 2 ^ 47 ≤ s := by
    rw [hs, Nat.le_sqrt]
    calc (2:ℕ) ^ 47 * 2 ^ 47 = 2 ^ 94 := by ring
      _ ≤ 2 ^ 95 := by norm_num
      _ ≤ N := hlo
  set k := (142 * s) / 100 with hk
  have hk1 : 142 * s < 100 * (k + 1) := by omega
  have hsq : 2 * (s * s) + 4 * s + 2 < (k + 1) * (k + 1) := by nlinarith
  have hexp : (s + 1) * (s + 1) = s * s + 2 * s + 1 := by ring
  have hm : Nat.sqrt (N + 2 ^ 95 - 1) < k + 1 := by
    rw [Nat.sqrt_lt']
    have : (k + 1) ^ 2 = (k + 1) * (k + 1) := by ring
    omega
  omega
