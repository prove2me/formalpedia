-- Prove2me | solution 1 for NumberTheory.ExclusiveChannel.concave_single_drop_le_of_equal_shares
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:58:24.034212+00:00
-- url     : https://prove2.me/submissions/7ca6d2fa-3c6f-4912-8daf-6e94a5615598

-- Sol generated from NumberTheory/ExclusiveChannelConvexity.lean
import Mathlib
import Definitions.Def_NumberTheory_ExclusiveChannelConvexity
import Definitions.Def_NumberTheory_ExclusiveChannelInterventions
import Theorems.Thm_NumberTheory_ExclusiveChannel_chord_le_of_convexOn
/-
# NET-30 / Catalog·NumberTheory — Where the saturation lives: the convexity
dichotomy of exclusive-block ablations

`NumberTheory.ExclusiveChannelInterventions` shows that an *affine* boundary
read-out is additive: the whole-block ablation drop equals the sum of the
single-coordinate drops, so the measured s = 13, k = 2 signature (all single
drops inside `±0.002`, block drop `0.2436`) is affinely impossible.  This file
locates the exact boundary of that no-go.

Model the read-out along the block ray as `φ (∑ i, s i)`, where `s i ≥ 0` is the
gain contributed by exclusive coordinate `i` and `φ : ℝ → ℝ` is an arbitrary
scalar nonlinearity (the saturating gate of the trained cell).  Write
`S = ∑ i, s i`, block drop `D = φ S - φ 0`, single drop `dᵢ = φ S - φ (S - s i)`.

* `chord_le_of_convexOn` / `le_chord_of_concaveOn`: the one-line chord
  inequality behind everything, `a * (φ S - φ 0) ≤ S * (φ S - φ (S - a))`
  for convex `φ` and `0 ≤ a ≤ S`, and its reverse for concave `φ`.
* `convex_block_drop_le_sum_single_drops`: **convex read-outs cannot hide the
  block.**  `D ≤ ∑ i, dᵢ`.  With affine `φ` this is the equality of the
  companion file; with convex `φ` it is still an upper bound, so a `k`-fold
  no-op tolerance `ε` caps the block drop at `k · ε`
  (`convex_block_drop_le_card_mul`).
* `concave_sum_single_drops_le_block_drop`: **concave (saturating) read-outs
  can.**  `∑ i, dᵢ ≤ D`, and the gap is unbounded.
* `concave_single_drop_le_share`: the quantitative saturation law
  `dᵢ ≤ (s i / S) · D`; with an equal split over `k` coordinates
  (`concave_single_drop_le_of_equal_shares`) every single drop is at most
  `D / k` **while the block drop stays `D`**.  This is the formal shape of the
  measured trend "self-sufficiency of single coordinates rises with `k`":
  under a saturating gate, redundancy is forced by concavity alone, at rate
  `1/k`, with no appeal to what the network learned.
* `s13_k2_no_convex_readout`, `s13_readout_defect_negative`: applied to the
  published numbers, the s = 13 arm is a **strict-concavity certificate**: the
  redundancy defect `∑ dᵢ - D` is measured at `≤ 0.004 - 0.2436 < 0`, which no
  convex — a fortiori no affine — read-out can produce.

The upshot for the round: "1-redundant but block-dependent" is not an exotic
coincidence, it is exactly the signature of a *saturated* boundary channel, and
it needs `k ≥ 2` (companion file) plus strict concavity (here).
-/


open NumberTheory.ExclusiveChannel

open Finset

variable {k : ℕ}

/-! ## The chord inequality -/


/-- Concave version of `chord_le_of_convexOn`. -/
theorem le_chord_of_concaveOn {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ Set.univ φ) {S a : ℝ}
    (hS : 0 < S) (ha : 0 ≤ a) (haS : a ≤ S) :
    S * (φ S - φ (S - a)) ≤ a * (φ S - φ 0) := by
  have hneg : ConvexOn ℝ Set.univ (fun x => -φ x) := hφ.neg
  have := chord_le_of_convexOn hneg hS ha haS
  simp only at this
  nlinarith

/-! ## Block drop versus single drops -/

/-- The block gain `S = ∑ i, s i` dominates each individual gain. -/
theorem le_sum_of_nonneg {s : Fin k → ℝ} (hs : ∀ i, 0 ≤ s i) (i : Fin k) :
    s i ≤ ∑ j, s j :=
  Finset.single_le_sum (fun j _ => hs j) (Finset.mem_univ i)




/-- **The saturation law, quantitative form.**  Under a concave read-out the
drop caused by ablating coordinate `i` is at most its *share* `s i / S` of the
whole-block drop. -/
theorem concave_single_drop_le_share {φ : ℝ → ℝ} (hφ : ConcaveOn ℝ Set.univ φ)
    {s : Fin k → ℝ} (hs : ∀ i, 0 ≤ s i) (hS : 0 < ∑ j, s j) (i : Fin k) :
    φ (∑ j, s j) - φ ((∑ j, s j) - s i)
      ≤ (s i / ∑ j, s j) * (φ (∑ j, s j) - φ 0) := by
  set S := ∑ j, s j with hSdef
  have h := le_chord_of_concaveOn hφ hS (hs i) (hSdef ▸ le_sum_of_nonneg hs i)
  rw [div_mul_eq_mul_div, le_div_iff₀ hS]
  linarith [h]


/-! ## The measured k = 2, s = 13 arm is a strict-concavity certificate -/








open NumberTheory.ExclusiveChannel in
theorem solution{φ : ℝ → ℝ} (hφ : ConcaveOn ℝ Set.univ φ)
    {S : ℝ} (hS : 0 < S) (hk : 0 < k) (i : Fin k)
    (s : Fin k → ℝ) (hsplit : ∀ j, s j = S / k) :
    φ (∑ j, s j) - φ ((∑ j, s j) - s i) ≤ (φ S - φ 0) / k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : ∀ j, 0 ≤ s j := fun j => by rw [hsplit j]; positivity
  have hsum : ∑ j, s j = S := by
    simp [hsplit, Finset.sum_const, Finset.card_univ]
    field_simp
  have hSpos : 0 < ∑ j, s j := by rw [hsum]; exact hS
  have h := concave_single_drop_le_share hφ hs hSpos i
  rw [hsum] at h ⊢
  rw [hsplit i] at h ⊢
  calc φ S - φ (S - S / k) ≤ (S / k / S) * (φ S - φ 0) := h
    _ = (φ S - φ 0) / k := by field_simp
