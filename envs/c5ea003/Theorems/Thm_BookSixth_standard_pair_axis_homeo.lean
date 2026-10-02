-- Prove2me | Theorems.Thm_BookSixth_standard_pair_axis_homeo
-- name    : BookSixth.standard_pair_axis_homeo
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T11:44:29.125924+00:00
-- url     : https://prove2.me/theorems/76d7233c-8aa1-4ab2-9925-3a5ac1b06c74
-- title:
--   Chapter 15 bridge: relabel two separated intervals on the real axis
-- statement:
--   Let two unit intervals on the real line be centered at $0\le a$ and at $b\ge3$, with at least unit distance between their centers. There is a jointly continuous path of real-line homeomorphisms, starting at the identity, whose endpoint translates the first interval to the interval centered at zero and the second interval to the interval centered at three.
--
--   The path translates the two outer intervals and linearly compresses only the intervening gap. This is the one-dimensional geometric core of the ordered pair-relabeling step used when extracting an unlinked pair from a larger ambient-isotopy witness. Separating this real-line construction from the coordinatewise lift makes the endpoint theorem a short adapter.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 100. Source-faithful one-dimensional ordered pair relabeling used by BookSixth.standard_pair_relabel_lt. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.standard_pair_axis_homeo
    (a b : ℝ) (ha : 0 ≤ a) (hb : 3 ≤ b) (hab : 3 ≤ b - a) :
    ∃ R : ℝ → ℝ ≃ₜ ℝ,
      Continuous (fun p : ℝ × ℝ => R p.1 p.2) ∧
      Continuous (fun p : ℝ × ℝ => (R p.1).symm p.2) ∧
      (∀ x, R 0 x = x) ∧
      (∀ u, -1 ≤ u → u ≤ 1 → R 1 (a + u) = u) ∧
      (∀ u, -1 ≤ u → u ≤ 1 → R 1 (b + u) = 3 + u) := by sorry
