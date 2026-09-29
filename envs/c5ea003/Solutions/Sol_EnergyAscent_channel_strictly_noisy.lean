-- Prove2me | solution 1 for EnergyAscent.channel_strictly_noisy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:29:12.692147+00:00
-- url     : https://prove2.me/submissions/9738284d-00c3-4a19-bd4d-75d6f19af5a2

-- Sol generated from Combinatorics/EnergyAscentChannel.lean
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters
import Definitions.Def_Combinatorics_EnergyAscentChannel
import Definitions.Def_Combinatorics_EnergyAscentFermatWindow
import Definitions.Def_Combinatorics_EnergyAscentPellSpine
import Theorems.Thm_EnergyAscent_branchLetter_eq_one_iff
import Theorems.Thm_EnergyAscent_bridge_nonvacuous
import Theorems.Thm_EnergyAscent_noisy_primitive
import Theorems.Thm_EnergyAscent_window_hit_ratio_bound

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


theorem noisy_isPT (k : ℤ) : IsPT (noisy k).1 (noisy k).2.1 (noisy k).2.2 := by
  unfold IsPT noisy; simp only; ring

theorem noisy_sorted {k : ℤ} (hk : 1 ≤ k) : (noisy k).1 ≤ (noisy k).2.1 := by
  simp only [noisy]; nlinarith

theorem noisy_pos {k : ℤ} (hk : 1 ≤ k) :
    0 < (noisy k).1 ∧ 0 < (noisy k).2.2 := by
  constructor <;> · simp only [noisy]; nlinarith

/-- The family lies in the middle ratio band, so it carries the letter `1`. -/
theorem noisy_letterOne {k : ℤ} (hk : 1 ≤ k) : LetterOne (noisy k) := by
  unfold LetterOne
  rw [branchLetter_eq_one_iff]
  simp only [noisy]
  constructor <;> nlinarith


/-- The family is admissible above the sensor scale. -/
theorem noisy_admissible {W k : ℤ} (hW : 0 < W) (hk : 15 * W ≤ k) (hj : ∃ j, k = 2 * j) :
    Admissible W (noisy k) := by
  obtain ⟨j, rfl⟩ := hj
  have hk1 : 1 ≤ 2 * j := by omega
  obtain ⟨hpa, hpc⟩ := noisy_pos hk1
  exact { pos_a := hpa
          sorted := noisy_sorted hk1
          pos_c := hpc
          pt := noisy_isPT _
          prim := noisy_primitive j
          scale := by simp only [noisy]; nlinarith }

/-- **The ceiling.**  The middle-band family is never inside the window: its leg
gap grows quadratically while the window is fixed.  Hence the letter does *not*
determine the window bit. -/
theorem noisy_not_hit {W k : ℤ} (hW : 0 < W) (hk : 15 * W ≤ k) : ¬ InWindow W (noisy k) := by
  have hk1 : (1 : ℤ) ≤ k := by omega
  intro hhit
  have hpa : (0 : ℤ) < (noisy k).1 := (noisy_pos hk1).1
  have hpb : (0 : ℤ) < (noisy k).2.1 := lt_of_lt_of_le hpa (noisy_sorted hk1)
  have hR := window_hit_ratio_bound (p := ((noisy k).1 : ℝ)) (q := ((noisy k).2.1 : ℝ))
    (by exact_mod_cast hpa) (by exact_mod_cast hpb) hhit
  have hZ : ((noisy k).2.1 - (noisy k).1) ^ 2 ≤ 4 * W * ((noisy k).1 + (noisy k).2.1) := by
    exact_mod_cast hR
  simp only [noisy] at hZ
  nlinarith [hZ, hk, hW, hk1, sq_nonneg k, sq_nonneg (k - 1)]


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
theorem solution(S : ℤ) :
    (∃ T : ℤ × ℤ × ℤ, S < T.2.1 ∧ Admissible 1 T ∧ InWindow 1 T ∧ LetterOne T) ∧
    (∃ T : ℤ × ℤ × ℤ, S < T.2.1 ∧ Admissible 1 T ∧ ¬ InWindow 1 T ∧ LetterOne T) := by
  constructor
  · obtain ⟨a, b, c, hSb, h112, hpa, hab, hpc, hpt, hprim, hhit, hletter, -⟩ :=
      bridge_nonvacuous S
    refine ⟨(a, b, c), hSb,
      { pos_a := hpa, sorted := hab, pos_c := hpc, pt := hpt, prim := hprim,
        scale := by show (112 : ℤ) * 1 ≤ b; omega }, ?_, hletter⟩
    show fermatOffset (a : ℝ) (b : ℝ) ≤ ((1 : ℤ) : ℝ)
    simpa using hhit
  · obtain ⟨j, hj1, hjS⟩ : ∃ j : ℤ, 8 ≤ j ∧ S < 20 * (2 * j) ^ 2 + 4 * (2 * j) := by
      refine ⟨max 8 S, le_max_left _ _, ?_⟩
      have h1 : (8 : ℤ) ≤ max 8 S := le_max_left _ _
      have h2 : S ≤ max 8 S := le_max_right _ _
      nlinarith
    refine ⟨noisy (2 * j), ?_,
      noisy_admissible one_pos (by omega) ⟨j, rfl⟩,
      noisy_not_hit one_pos (by omega), noisy_letterOne (by omega)⟩
    simp only [noisy]
    nlinarith [hjS, hj1]
