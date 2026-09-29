-- Prove2me | solution 1 for SpikeOrigin.card_lowBand_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:35:59.261402+00:00
-- url     : https://prove2.me/submissions/b28ea692-113d-4e1b-b905-dca674c8a73a

-- Sol generated from Cryptography/SpikeOriginCounting.lean
import Mathlib
import Definitions.Def_Cryptography_SpikeOriginDegeneracy
import Theorems.Thm_SpikeOrigin_card_lowBand
import Theorems.Thm_SpikeOrigin_cut_le_window
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
    11 * Nat.sqrt N ≤
      50 * (((Finset.Ioc (Nat.sqrt N) (3 * Nat.sqrt N)).filter
        (fun j => resid N j < 2 ^ 95)).card) := by
  set s := Nat.sqrt N with hs
  have hcard := card_lowBand N (2 ^ 95) (by positivity)
  rw [min_eq_right (cut_le_window hlo hhi), ← hs] at hcard
  set m := Nat.sqrt (N + 2 ^ 95 - 1) with hm
  have h1 : s * s ≤ N := sqrt_sq_le N
  have hup : N < (s + 1) * (s + 1) := by
    have := Nat.lt_succ_sqrt' N
    simpa [hs, pow_two] using this
  -- `s` is large: `s ≥ 2⁴⁷`
  have hslarge : 2 ^ 47 ≤ s := by
    rw [hs, Nat.le_sqrt]
    calc (2:ℕ) ^ 47 * 2 ^ 47 = 2 ^ 94 := by ring
      _ ≤ 2 ^ 95 := by norm_num
      _ ≤ N := hlo
  -- the ceiling `k = ⌈1.22 s⌉` still lies below the cut point
  set k := (61 * s + 49) / 50 with hk
  have hk1 : 50 * k ≥ 61 * s := by omega
  have hk2 : 50 * k ≤ 61 * s + 49 := by omega
  have hhalf : 2 * (2 ^ 95 : ℕ) ≥ N := by omega
  have hkm : k ≤ m := by
    rw [hm, Nat.le_sqrt]
    -- `2500 k² ≤ (61 s + 49)² ≤ 3721 s² + 5978 s + 2401 ≤ 2500 (N + 2⁹⁵ − 1)`
    have hkk : 2500 * (k * k) ≤ (61 * s + 49) * (61 * s + 49) := by nlinarith
    have hgoal : (61 * s + 49) * (61 * s + 49) ≤ 2500 * (N + 2 ^ 95 - 1) := by
      have hN2 : 2 ^ 95 ≤ N := hlo
      have hsub : N + 2 ^ 95 - 1 ≥ N + (N / 2) - 1 := by omega
      have hexp : (61 * s + 49) * (61 * s + 49) = 3721 * (s * s) + 5978 * s + 2401 := by ring
      have hNs : 3721 * (s * s) ≤ 3721 * N := Nat.mul_le_mul_left _ h1
      have hbig : 5978 * s + 2401 + 3721 * N ≤ 2500 * (N + 2 ^ 95 - 1) := by
        have h2 : 2500 * (N + 2 ^ 95 - 1) ≥ 2500 * N + 1250 * N - 2500 := by omega
        have h3 : 5978 * s + 10000 ≤ 29 * N := by
          have : s ≤ N := Nat.sqrt_le_self N
          nlinarith [hslarge, hlo]
        omega
      omega
    have hfin := le_trans hkk hgoal
    omega
  omega
