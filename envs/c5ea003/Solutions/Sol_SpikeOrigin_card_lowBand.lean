-- Prove2me | solution 1 for SpikeOrigin.card_lowBand
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:04:35.894595+00:00
-- url     : https://prove2.me/submissions/01daa227-c563-4cd9-86b7-f2365d706025

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

lemma lt_sq_of_sqrt_lt {N j : ℕ} (hj : Nat.sqrt N < j) : N < j ^ 2 :=
  lt_of_lt_of_le (Nat.lt_succ_sqrt' N) (Nat.pow_le_pow_left hj 2)


/-- Membership in the low band `v < T` is exactly the positional condition
`j ≤ ⌊√(N + T − 1)⌋`. -/
theorem resid_lt_iff {N T j : ℕ} (hT : 0 < T) (hj : Nat.sqrt N < j) :
    resid N j < T ↔ j ≤ Nat.sqrt (N + T - 1) := by
  have hN : N < j ^ 2 := lt_sq_of_sqrt_lt hj
  have hstep : resid N j < T ↔ j * j ≤ N + T - 1 := by
    simp only [resid, pow_two] at *
    omega
  rw [hstep, Nat.le_sqrt]

/-- **The excluded (tiny-residue) set is a left-edge interval.** -/
theorem lowBand_eq_Ioc (N T : ℕ) (hT : 0 < T) :
    ((Finset.Ioc (Nat.sqrt N) (3 * Nat.sqrt N)).filter (fun j => resid N j < T))
      = Finset.Ioc (Nat.sqrt N) (min (3 * Nat.sqrt N) (Nat.sqrt (N + T - 1))) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_Ioc, le_min_iff]
  constructor
  · rintro ⟨⟨hj1, hj2⟩, hv⟩
    exact ⟨hj1, hj2, (resid_lt_iff hT hj1).1 hv⟩
  · rintro ⟨hj1, hj2, hj3⟩
    exact ⟨⟨hj1, hj2⟩, (resid_lt_iff hT hj1).2 hj3⟩


/-! ## How small the tiny channel gets -/


/-! ## The excluded interval strictly contains the first decile (96-bit case) -/


variable {N : ℕ}







/-! ## Monotone law for the continuum crossing position -/



open SpikeOrigin in
theorem solution(N T : ℕ) (hT : 0 < T) :
    ((Finset.Ioc (Nat.sqrt N) (3 * Nat.sqrt N)).filter (fun j => resid N j < T)).card
      = min (3 * Nat.sqrt N) (Nat.sqrt (N + T - 1)) - Nat.sqrt N := by
  rw [lowBand_eq_Ioc N T hT, Nat.card_Ioc]
