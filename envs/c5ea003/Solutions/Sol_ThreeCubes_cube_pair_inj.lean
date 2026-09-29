-- Prove2me | solution 1 for ThreeCubes.cube_pair_inj
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:37:09.306615+00:00
-- url     : https://prove2.me/submissions/56e73b33-e57d-4e8e-91f2-3e8e57bc5871

-- Sol generated from Probability/LowerBounds.lean
import Mathlib
import Definitions.Def_Probability_Density
import Definitions.Def_Probability_LowerBounds
import Definitions.Def_Probability_Rational

/-!
# Unconditional lower bounds for sums of three cubes

`Probability.ThreeCubes.Density` gives the *upper* bound: at most `7/9` of all integers are
sums of three cubes (`ThreeCubes.card_isSumOfThreeCubes_le`), and
`ThreeCubes.densitySevenNinths_iff_hasse` shows that the matching lower bound — i.e. density
exactly `7/9` — is *equivalent* to the Hasse principle for the affine cubic surface, hence
completely out of reach at present.

This file proves the strongest lower bound that is unconditional, namely a power-saving one.
Counting the values `k³ + m³` with `K³ ≤ k < 2K³` and `0 ≤ m ≤ K²`, the "small" cube `m³` is
always smaller than the gap `(k+1)³ - k³ = 3k² + 3k + 1`, so `k` is recoverable from the value
as `⌊n^{1/3}⌋` and the parametrisation is *injective*
(`ThreeCubes.cube_pair_inj`).  This produces `K³(K²+1)` distinct representable integers below
`9K⁹`, i.e.

* `ThreeCubes.repCount_ge` : `K⁵ ≤ repCount (9K⁹)`, an `≫ N^{5/9}` lower bound for the
  counting function `repCount N = #{n ≤ N : n is a sum of three cubes}`.

The exponent `5/9` is exactly the classical elementary bound: `3/9` comes from the cubes
themselves and the extra `2/9` from the `k^{2/3}`-many admissible small cubes.  Any improvement
beyond the trivial multiplicativity of this construction requires genuine control of the
representation multiplicity, which is the content of Conjecture 3 of `FUTURE_DIRECTIONS.md`.

The last section records the sharp contrast with the *rational* problem: four rational cubes
always suffice, by a one-line identity (`ThreeCubes.isSumOfFourRationalCubes`), whereas over
`ℤ` the analogous statement for four cubes is open.
-/

open ThreeCubes

open Finset

/-! ### An injective two-parameter family of sums of two cubes -/

/-- If `k ≥ K³` and `m ≤ K²` then the "small" cube `m³` is smaller than the gap between two
consecutive cubes at `k`.  This is the engine of the injectivity below. -/
theorem small_cube_lt_gap {K k m : ℕ} (hk : K ^ 3 ≤ k) (hm : m ≤ K ^ 2) :
    m ^ 3 < 3 * k ^ 2 + 3 * k + 1 := by
  have h1 : m ^ 3 ≤ (K ^ 2) ^ 3 := Nat.pow_le_pow_left hm 3
  have h2 : (K ^ 3) ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left hk 2
  have h3 : (K ^ 2) ^ 3 = (K ^ 3) ^ 2 := by ring
  omega











/-! ### Four rational cubes always suffice -/




open ThreeCubes in
theorem solution{K k m k' m' : ℕ} (hk : K ^ 3 ≤ k) (hm : m ≤ K ^ 2)
    (hk' : K ^ 3 ≤ k') (hm' : m' ≤ K ^ 2) (h : k ^ 3 + m ^ 3 = k' ^ 3 + m' ^ 3) :
    k = k' ∧ m = m' := by
  have key : ∀ a b c d : ℕ, K ^ 3 ≤ a → b ≤ K ^ 2 → a < c →
      a ^ 3 + b ^ 3 < c ^ 3 + d ^ 3 := by
    intro a b c d ha hb hac
    have hgap : b ^ 3 < 3 * a ^ 2 + 3 * a + 1 := small_cube_lt_gap ha hb
    have hmono : (a + 1) ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left hac 3
    have hexp : (a + 1) ^ 3 = a ^ 3 + (3 * a ^ 2 + 3 * a + 1) := by ring
    omega
  have hkk : k = k' := by
    rcases lt_trichotomy k k' with hlt | heq | hgt
    · exact absurd h (Nat.ne_of_lt (key k m k' m' hk hm hlt))
    · exact heq
    · exact absurd h.symm (Nat.ne_of_lt (key k' m' k m hk' hm' hgt))
  subst hkk
  have hm3 : m ^ 3 = m' ^ 3 := by omega
  exact ⟨rfl, Nat.pow_left_injective (by norm_num) hm3⟩
