-- Prove2me | solution 1 for EnergyAscent.empirical_positive_dependence
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:31:01.309104+00:00
-- url     : https://prove2.me/submissions/fbfd5a91-3f3c-4469-83eb-ec8022c4617b

-- Sol generated from Combinatorics/EnergyAscentChannel.lean
import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentBerggrenLetters
import Definitions.Def_Combinatorics_EnergyAscentChannel
import Definitions.Def_Combinatorics_EnergyAscentPellSpine
import Theorems.Thm_EnergyAscent_window_hit_determines_berggren_letter

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




/-- **Zero-error side of the channel.**  A window hit determines the letter. -/
theorem inWindow_letterOne {W : ℤ} (hW : 0 < W) {T : ℤ × ℤ × ℤ}
    (hA : Admissible W T) (hhit : InWindow W T) : LetterOne T :=
  (window_hit_determines_berggren_letter hA.pos_a hA.sorted hA.pos_c hA.pt hA.prim hW
    hA.scale hhit).1


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
theorem solution{W : ℤ} (hW : 0 < W)
    (F : Finset (ℤ × ℤ × ℤ)) (hF : ∀ T ∈ F, Admissible W T)
    (hhit : ∃ T ∈ F, InWindow W T) (hbad : ∃ T ∈ F, ¬ LetterOne T) :
    (F.filter (fun T => LetterOne T)).card * (F.filter (fun T => InWindow W T)).card <
      (F.filter (fun T => InWindow W T ∧ LetterOne T)).card * F.card := by
  have hsub : F.filter (fun T => InWindow W T) = F.filter (fun T => InWindow W T ∧ LetterOne T) := by
    apply Finset.filter_congr
    intro T hT
    exact ⟨fun h => ⟨h, inWindow_letterOne hW (hF T hT) h⟩, fun h => h.1⟩
  obtain ⟨T₀, hT₀F, hT₀⟩ := hhit
  have hpos : 0 < (F.filter (fun T => InWindow W T)).card :=
    Finset.card_pos.mpr ⟨T₀, Finset.mem_filter.mpr ⟨hT₀F, hT₀⟩⟩
  obtain ⟨T₁, hT₁F, hT₁⟩ := hbad
  have hlt : (F.filter (fun T => LetterOne T)).card < F.card := by
    apply Finset.card_lt_card
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro hcon
    exact hT₁ (Finset.mem_filter.mp (hcon hT₁F)).2
  calc (F.filter (fun T => LetterOne T)).card * (F.filter (fun T => InWindow W T)).card
      < F.card * (F.filter (fun T => InWindow W T)).card := by
        exact (Nat.mul_lt_mul_right hpos).mpr hlt
    _ = (F.filter (fun T => InWindow W T ∧ LetterOne T)).card * F.card := by
        rw [← hsub]; ring
