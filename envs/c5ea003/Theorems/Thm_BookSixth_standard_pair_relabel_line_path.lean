-- Prove2me | Theorems.Thm_BookSixth_standard_pair_relabel_line_path
-- name    : BookSixth.standard_pair_relabel_line_path
-- status  : Open
-- author  : @WillR
-- created : 2026-09-25T11:48:22.16337+00:00
-- url     : https://prove2.me/theorems/cf4879ad-d6cf-452a-809a-f0770420e5ba
-- title:
--   Piecewise relabeling of two ordered centers on the real line
-- statement:
--   For i < j, there is a continuous path of increasing homeomorphisms of the real line that starts at the identity and performs the source-faithful relabeling of the two ordered centers. If tau(t) = max 0 (min t 1), the center 3i moves to 3i(1-tau(t)), while the center 3j moves to 3j(1-tau(t)) + 3tau(t). Thus at time one the centers are 0 and 3, and the displacement of each circle is a translation; the intervening gap alone is compressed. The other two coordinates are unchanged when this path is lifted to three dimensions, so the unit-circle radii are preserved.
--
--   The all-time formulas are part of the statement so that a generic ambient isotopy, or an anisotropic affine scaling that changes a circle into an ellipse, cannot replace the intended piecewise-linear construction.
--
--   **Formalization Note.** The existential statement records the path, continuity in both directions, the identity at time zero, and the two moving-center laws. The endpoint relabelings follow by taking t = 1.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 100. Source-faithful real-line relabeling used by the ordered two-circle ambient-isotopy adapter. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib

theorem BookSixth.standard_pair_relabel_line_path
    {i j : ℕ} (hij : i < j) :
    ∃ F : ℝ → (ℝ ≃ₜ ℝ),
      Continuous (fun p : ℝ × ℝ => (F p.1) p.2) ∧
      Continuous (fun p : ℝ × ℝ => (F p.1).symm p.2) ∧
      (∀ x, F 0 x = x) ∧
      (∀ t s, F t (3 * (i : ℝ) + Real.cos s) =
        3 * (i : ℝ) * (1 - max 0 (min t 1)) + Real.cos s) ∧
      (∀ t s, F t (3 * (j : ℝ) + Real.cos s) =
        3 * (j : ℝ) * (1 - max 0 (min t 1)) + 3 * max 0 (min t 1) + Real.cos s) := by sorry
