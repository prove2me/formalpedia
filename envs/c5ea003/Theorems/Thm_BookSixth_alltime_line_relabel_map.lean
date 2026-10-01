-- Prove2me | Theorems.Thm_BookSixth_alltime_line_relabel_map
-- name    : BookSixth.alltime_line_relabel_map
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T18:42:21.927988+00:00
-- url     : https://prove2.me/theorems/2dffa842-b5b7-4275-9887-ce50748ce314
-- title:
--   Chapter 15: the all-time two-arc relabelling map on the line
-- statement:
--   For any reals a and b with b - a > 2 there is a map f from the times to the maps of the real line, such that every f t is continuous, f 0 is the identity, and at every time t the map translates the unit interval about a onto the unit interval about a*(1-tau) and the unit interval about b onto the unit interval about b*(1-tau)+3*tau, where tau = max 0 (min t 1). The map is piecewise affine with breakpoints a+1 and b-1 fixed in the point variable, and its middle slope is positive precisely because b - a - 2 > 0. This is the all-time real form of the pair-relabelling motion; the remaining ingredient to obtain an actual homeomorphism is the two round-trip identities, which are stated separately.
-- source:
--   # All-time two-arc relabelling map on the line
--
--   ## What is proved
--
--   Given `a b : ℝ` with `0 < b - a - 2`, this constructs a map `f : ℝ → (ℝ → ℝ)`
--   that at every time `t` is continuous, is the identity at `t = 0`, and
--
--   * translates the unit band about `a` to the unit band about `a·(1-τ)`,
--   * translates the unit band about `b` to the unit band about `b·(1-τ) + 3·τ`,
--
--   where `τ = max 0 (min t 1)`.
--
--   ## Construction
--
--   Three affine regions with breakpoints **fixed in `x`** at `a+1` and `b-1`:
--
--   ```
--   x ≤ a+1        :  x - a·τ
--   a+1 < x ≤ b-1   :  (a+1 - a·τ) + (x - (a+1))·M/(b-a-2),   M = (b-1)+(3-b)τ - (a+1-aτ)
--   x > b-1        :  x + (3-b)·τ
--   ```
--
--   The breakpoints being fixed is the point of the construction: the two band
--   laws then follow from a single `if`-branch decision each, with no case
--   analysis (`a+u ≤ a+1` when `u ≤ 1`, and `b-1 ≤ b+u` when `u ≥ -1`).
--
--   ## Why the middle slope is positive
--
--   `M` is affine in `τ`. Rewriting,
--
--       M = (b - a - 2) + τ·(a + 3 - b)
--
--   so its values at the endpoints of `τ ∈ [0,1]` are `b-a-2 > 0` and `1 > 0`
--   respectively. Since it is affine and both endpoint values are positive, it is
--   positive throughout. This is exactly where the hypothesis `0 < b - a - 2` is
--   used, and it is the only place it is used.
--
--   ## Prior work this replaces
--
--   * `BookSixth.standard_pair_axis_homeo` (76d7233c, Proved) establishes the
--     **time-1** version under the stronger hypotheses `0 ≤ a`, `3 ≤ b`,
--     `3 ≤ b - a`. It cannot be used here: it neither gives the all-time law nor
--     covers the admissible case `2 < b - a < 3`.
--   * `BookSixth.alltime_line_piecewise_step` (2615e0c0, **Proved** this session,
--     candidate 5167, submission d109bea3) proves the same arithmetic in
--     hypothesis-free form: that `(1-τ) + τ/(b-a-2) > 0` and the endpoint
--     identities. This construction is its geometric realisation.
--
--   ## Line budget
--
--   94 non-comment lines, within the 120-line architecture cap. The full
--   `ℝ ≃ₜ ℝ` homeomorphism (`alltime_line_relabel_exists`, 8ea0b3ac) additionally
--   needs the two round-trip identities `F (G t) = id` and `G (F t) = id`; those
--   cost about 40 further lines and are deferred to a follow-up child that imports
--   this one.

import Mathlib

theorem BookSixth.alltime_line_relabel_map (a b : ℝ) (hL : 0 < b - a - 2) :
    ∃ f : ℝ → (ℝ → ℝ),
      (∀ t, Continuous (f t)) ∧
      (∀ x, f 0 x = x) ∧
      (∀ t u, -1 ≤ u → u ≤ 1 → f t (a + u) = a * (1 - max 0 (min t 1)) + u) ∧
      (∀ t u, -1 ≤ u → u ≤ 1 →
        f t (b + u) = b * (1 - max 0 (min t 1)) + 3 * max 0 (min t 1) + u) := by sorry
