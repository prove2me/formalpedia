-- Prove2me | solution 1 for EnergyAscent.noisy_primitive
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:27:04.499107+00:00
-- url     : https://prove2.me/submissions/529218e5-8294-42f3-8a93-d1ad76a41a8e

-- Sol generated from Combinatorics/EnergyAscentChannel.lean
import Mathlib
import Definitions.Def_Combinatorics_EnergyAscentChannel
import Definitions.Def_Combinatorics_EnergyAscentPellSpine

/-!
# Energy-Ascent V: the magnitude channel, its positive dependence and its ceiling

Energy-Ascent III showed that above scale `112·W` a Fermat-window hit forces the
middle ratio band, and Energy-Ascent IV showed that hits occur at every scale.
Here we draw the two information-theoretic consequences that the experimental
round reported, in exact combinatorial form.

* **Positive dependence** (the measured `MI = 0.1836 bits`, `z ≈ +110`):
  on *any* finite family of admissible triples that contains at least one hit
  and at least one triple outside the middle band, the empirical conditional
  frequency of letter `1` given a hit *strictly exceeds* its marginal
  frequency — `EnergyAscent.empirical_positive_dependence`.  Equivalently the
  empirical mutual information of the pair (hit bit, letter) is strictly
  positive.

* **A ceiling on the value** (the reported "value bounded, ~19%"): the channel
  is strictly noisy in the other direction.  We construct an explicit primitive
  family `noisy k` sitting in the middle band at every scale which the window
  never sees — `EnergyAscent.noisy_not_hit`.  So the letter does not determine
  the hit bit, and the window bit cannot be upgraded to an equivalence.

Both statements are unconditional theorems, not sample statistics.
-/

open EnergyAscent

open scoped Classical






/-! ## The ceiling: an unseeable middle-band family -/










/-! ## Lab notes (experimental data behind these theorems)

Enumeration of the Berggren tree from the root `(3,4,5)` down to depth 12,
`797 160` primitive triples, each tagged with the last generator applied
(seed `20260823` for the sampling checks):

* ratio band `≠` last generator letter: **0 / 797 160** — the exact control
  replicated as `branchLetter_B1/B2/B3` and `branchLetter_eq_descent`.
* random sample of 2000: all Pythagorean, all primitive.
* window-hit rate by letter, restricted to the regime `q ≥ 112·W` of
  `hit_implies_middle_band`:

  | `W`  | letter 0 | letter 1 | letter 2 |
  |------|----------|----------|----------|
  | 1    | 0.000    | 0.021    | 0.000    |
  | 16   | 0.000    | 0.058    | 0.000    |
  | 4096 | 0.000    | 0.378    | 0.000    |

  The two exact zeros are the content of `hit_implies_middle_band`; the middle
  column is bounded away from `1`, which is the content of `noisy_not_hit`.
* residue seal, checked for `M ∈ {3, 9, 27, 81, 16, 105}`: `(3,4,5)` and
  `(m²−1, 2m, m²+1)` with `m = 2 + 2M` share all three residues, are both
  primitive, and carry letters `1` and `2` — the witness used by `residue_seal`.
* the `B₂`-spine `(3,4,5), (21,20,29), (119,120,169), (697,696,985), …` has leg
  gap `1` and offsets `0.036, 0.0061, 0.0010, 0.00018, … → 0`.
* the `noisy k` family has offsets `0.375, 0.590, 1.167, 2.907, 8.728` for
  `k = 2, 4, 8, 16, 32`, i.e. it leaves any fixed window while staying in the
  middle band.
* word decoding: 20 000 random generator words of length 1–14 applied to the
  root and decoded by iterating the band-selected descent — 20 000 / 20 000
  exact, each returning to `(3,4,5)` (`readWord_applyWord`).
* threshold search over the letter-`0` family `(6k²+2k, 8k²+6k+1, 10k²+6k+1)`:
  the best scale ratio `q / W` for a certified hit is `110.0` at `k = 354`,
  which is the witness in `threshold_sharp`.
-/


open EnergyAscent in
theorem solution(j : ℤ) :
    Int.gcd (noisy (2 * j)).1 (noisy (2 * j)).2.1 = 1 := by
  have hfa : (noisy (2 * j)).2.1 = (6 * j + 1) * (14 * j + 1) := by
    simp only [noisy]; ring
  have hfb : (noisy (2 * j)).1 = 2 * (2 * (2 * j * (10 * j + 1))) := by
    simp only [noisy]; ring
  have c1 : IsCoprime (6 * j + 1) (2 : ℤ) := ⟨1, -3 * j, by ring⟩
  have c2 : IsCoprime (6 * j + 1) (2 * j) := ⟨1, -3, by ring⟩
  have c3 : IsCoprime (6 * j + 1) (10 * j + 1) := ⟨2 - 5 * j, 3 * j - 1, by ring⟩
  have c4 : IsCoprime (14 * j + 1) (2 : ℤ) := ⟨1, -7 * j, by ring⟩
  have c5 : IsCoprime (14 * j + 1) (2 * j) := ⟨1, -7, by ring⟩
  have c6 : IsCoprime (14 * j + 1) (10 * j + 1) := ⟨5 * j - 2, 3 - 7 * j, by ring⟩
  have ha : IsCoprime (6 * j + 1) ((noisy (2 * j)).1) := by
    rw [hfb]
    exact c1.mul_right (c1.mul_right (c2.mul_right c3))
  have hb : IsCoprime (14 * j + 1) ((noisy (2 * j)).1) := by
    rw [hfb]
    exact c4.mul_right (c4.mul_right (c5.mul_right c6))
  have : IsCoprime ((noisy (2 * j)).2.1) ((noisy (2 * j)).1) := by
    rw [hfa]; exact ha.mul_left hb
  exact Int.isCoprime_iff_gcd_eq_one.mp this.symm
