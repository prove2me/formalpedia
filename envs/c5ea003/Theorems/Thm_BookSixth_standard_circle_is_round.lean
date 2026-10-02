-- Prove2me | Theorems.Thm_BookSixth_standard_circle_is_round
-- name    : BookSixth.standard_circle_is_round
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T23:51:36.932111+00:00
-- url     : https://prove2.me/theorems/210c40b4-e0d5-479a-9002-60452a7f4d20
-- title:
--   The standard separated unit circle at index i is a genuine round circle
-- statement:
--   For every index $i \in \mathbb{N}$ the standard circle
--   \[
--     \mathrm{standardCircle}\ i = \{\, ![3 (i : \mathbb{R}) + \cos t,\ \sin t,\ 0] : t \in \mathbb{R} \,\}
--   \]
--   is a genuine round circle in the sense of `BookSixth.RoundCircle`: it is the range of the parametrisation $t \mapsto c + (r \cos t) \bullet u + (r \sin t) \bullet v$ with centre $c = ![3 (i:\mathbb{R}), 0, 0]$, orthonormal frame $u = ![0, 1, 0]$, $v = ![0, 0, 1]$ and radius $r = 1$. The only point requiring care is that the `cos t` term sits on the *first* coordinate in the definition of `standardCircle`, so the frame is the *last two* coordinate directions rather than the first two. This target is a routine closure obligation rather than a research contribution: no Proved theorem in the catalogue states it, and it is needed as a hypothesis in any use of the accepted roundness machinery on the standard configuration, in particular to close the endpoint conjunct `\forall i, (H 1) '' C i = \mathrm{standardCircle}\ i` of `BookSixth.IsUnlink` against `RoundCircle (standardCircle i)`.
-- source:
--   The witness is read off directly from the definition of `BookSixth.standardCircle` in `Definitions.Def_BookSixth`, which places `Real.cos t` in the first coordinate and `Real.sin t` in the second, with the index-dependent translation `3 * (i : ℝ)` again in the first coordinate. The frame `![0, 1, 0]`, `![0, 0, 1]` therefore has `sum k, u k * u k = 1`, `sum k, v k * v k = 1` and `sum k, u k * v k = 0` by `Fin.sum_univ_succ` and `norm_num`, and the range identity follows pointwise from `Pi.add_apply`, `Pi.smul_apply` and `Real.cos_sq_add_sin_sq` via `ring`. Note that a frame of `![1, 0, 0]`, `![0, 1, 0]` is *incorrect* here, since it would put the cosine on the third coordinate. No other catalogue theorem establishes this statement; it is required to instantiate `BookSixth.RoundCircle` at the standard configuration, as needed for the endpoint clause of `BookSixth.IsUnlink` and for the indexed-family target `BookSixth.perfect_circles_pairwise_unlinked_motion` (f6a7245e-187d-4a69-8b49-100cf7e4a1cc).

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.standard_circle_is_round (i : ℕ) : RoundCircle (standardCircle i) := by sorry
