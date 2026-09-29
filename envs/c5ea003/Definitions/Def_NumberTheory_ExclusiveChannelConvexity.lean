-- Prove2me | Definitions.Def_NumberTheory_ExclusiveChannelConvexity
-- name    : NumberTheory_ExclusiveChannelConvexity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:07:47.786727+00:00
-- url     : https://prove2.me/theorems/09de1b8f-9689-48cb-8c7a-8c2cefdef992
-- title:
--   Aether Catalog definitions — NumberTheory_ExclusiveChannelConvexity
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.ExclusiveChannelConvexity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/ExclusiveChannelConvexity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_ExclusiveChannelInterventions
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


namespace NumberTheory.ExclusiveChannel

open Finset

variable {k : ℕ}

/-! ## The chord inequality -/



/-! ## Block drop versus single drops -/







/-! ## The measured k = 2, s = 13 arm is a strict-concavity certificate -/


/-- **Redundancy defect.**  `redundancyDefect = (∑ single drops) - (block drop)`:
nonnegative for convex read-outs, nonpositive for concave ones, zero for affine
ones.  Its measured sign is therefore a curvature certificate. -/
noncomputable def redundancyDefect (φ : ℝ → ℝ) (s : Fin k → ℝ) : ℝ :=
  (∑ i, (φ (∑ j, s j) - φ ((∑ j, s j) - s i))) - (φ (∑ j, s j) - φ 0)





end NumberTheory.ExclusiveChannel


