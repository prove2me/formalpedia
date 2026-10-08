-- Prove2me | Theorems.Thm_BookSixth_pair_relabel_line_alltime_interpolation
-- name    : BookSixth.pair_relabel_line_alltime_interpolation
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T16:24:18.564223+00:00
-- url     : https://prove2.me/theorems/afecf75a-b9fb-4d1e-922d-26c9c2e70dc9
-- title:
--   Chapter 15: lift an endpoint relabeling of the real line to an all-time path by time interpolation
-- statement:
--   **The all-time path lemma.** Suppose `g` is an increasing homeomorphism of the real line that already performs the endpoint relabeling, in the sense that the unit circle centred at `a` is sent to the unit circle centred at `0`, and the unit circle centred at `b` is sent to the unit circle centred at `3`: for every `u` in `[-1, 1]` one has `g (a + u) = u` and `g (b + u) = 3 + u`. Then there is a path of increasing homeomorphisms of the line, starting at the identity, whose relabeling law holds at **every** time, not merely at time one.
--
--   The path is the time interpolation
--
--   $$F_t(x) = (1 - \tau(t))\, x + \tau(t)\, g(x), \qquad \tau(t) = \max 0\min t 1.$$
--
--   The point is that the two circle laws are preserved under this interpolation for an elementary reason: `g` is affine on any interval, so wherever the two circles sit, the identity `((1-τ) id + τ g) (a + u)` expands to `(1-τ)(a + u) + τ g (a + u)`, and the hypothesis `g (a + u) = u` collapses the second term to `τ u`, leaving `a (1 - τ) + u`. The same computation at `b` uses `g (b + u) = 3 + u` and leaves `b (1 - τ) + 3 τ + u`. No case analysis on which piece of the piecewise-linear `g` is in force is needed, because the interpolation commutes with every affine piece of `g` and `a + u` and `b + u` lie in the two tail pieces where the relevant affine formula is simply `x ↦ x - a` and `x ↦ x + (3 - b)`.
--
--   The path starts at the identity because `τ 0 = 0`, and it saturates at `g` because `τ 1 = 1`. Each `F_t` is an increasing bijection: on every affine piece of `g` with slope `m > 0` the composite has slope `(1 - τ) + τ m > 0`, and on the two tails of `g`, where `m = 1`, the slope is exactly `1`, so the two ends are preserved.
--
--   This is the lemma that turns the Proved endpoint theorem `BookSixth.standard_pair_axis_homeo` into the all-time statement `BookSixth.standard_pair_relabel_line_path`, which demands the relabeling law at every time so that neither a generic ambient isotopy nor an anisotropic affine rescaling can substitute for the intended piecewise-linear motion.
-- source:
--   Chapter 15 of the sixth-edition notes: the moving-centre construction for the ordered pair of standard circles. The book compresses only the gap between the two circles while translating each circle rigidly, so each circle is a translate of the standard one at every time and the all-time formulas pin down the motion. The technical difficulty is that the endpoint version of the relabeling is easy to establish, whereas the statement in the book requires the same law at every time; this lemma supplies the interpolation that bridges the two.

import Mathlib

theorem BookSixth.pair_relabel_line_alltime_interpolation (a b : ℝ) (g : ℝ ≃ₜ ℝ)
    (hglo : ∀ u, -1 ≤ u → u ≤ 1 → g (a + u) = u)
    (hghi : ∀ u, -1 ≤ u → u ≤ 1 → g (b + u) = 3 + u) :
    ∃ F : ℝ → (ℝ ≃ₜ ℝ),
      Continuous (fun p : ℝ × ℝ => (F p.1) p.2) ∧
      Continuous (fun p : ℝ × ℝ => (F p.1).symm p.2) ∧
      (∀ x, F 0 x = x) ∧
      (∀ t u, -1 ≤ u → u ≤ 1 →
        F t (a + u) = a * (1 - max 0 (min t 1)) + u) ∧
      (∀ t u, -1 ≤ u → u ≤ 1 →
        F t (b + u) = b * (1 - max 0 (min t 1)) + 3 * max 0 (min t 1) + u) := by sorry
