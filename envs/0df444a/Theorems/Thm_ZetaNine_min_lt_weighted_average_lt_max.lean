-- Prove2me | Theorems.Thm_ZetaNine_min_lt_weighted_average_lt_max
-- name    : ZetaNine.min_lt_weighted_average_lt_max
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T03:25:17.300562+00:00
-- url     : https://prove2.me/theorems/ce7cd721-4855-4529-9818-750413cf71e6
-- title:
--   Positive weights sandwich their weighted average
-- statement:
--   ## Positive weights sandwich their weighted average
--
--   Let $w,r:\{0,1,2,3,4\}\to\mathbb{R}$ with $w_j>0$ for every $j$, $\sum_j w_j=1$, and
--   suppose $r$ is not constant. Then the weighted average
--   $S=\sum_j w_j\,r_j$ is strictly above one of the sampled values and strictly below
--   another:
--
--   $$\exists j,\ r_j<S
--   \qquad\text{and}\qquad
--   \exists j,\ S<r_j .$$
--
--   **Why.** If every $r_j\ge S$, then $S=\sum_j w_jr_j\ge\sum_j w_j S=S$, and equality in
--   the intermediate step forces $r_j-S=0$ for every $j$ — because the summands
--   $w_j(r_j-S)$ are nonnegative and add up to $0$ and each $w_j$ is nonzero. That makes
--   $r$ constant, contradicting the hypothesis. The other inequality is the same argument
--   with the sign reversed. No compactness or ordering of the index set is used.
--
--   **Scope.** This is the ordering heart of local node **FI**. In the construction the
--   five weights are the exact positive cubature weights of FQ and the two coordinate sums
--   are normalised to $1$ and $\zeta(9)$, so the true value is a weighted average of the
--   five sampled ratios and the lemma places it strictly between their minimum and their
--   maximum. The non-constancy hypothesis is where the rank-two non-degeneracy of the
--   inverse image enters; if all sampled ratios coincided there would be no interval at
--   all. The lemma says nothing about the *width* of the interval, about the exponent
--   $-10.1109$ rate, or about the open question whether the moving shortest output avoids
--   the interval — that is target T5.
-- source:
--   Local zeta9 research note, roadmap/research/five-point-ratio-window.md, strict five-sample ratio window, 2026-09-25

import Mathlib

namespace ZetaNine

theorem min_lt_weighted_average_lt_max
    (w r : Fin 5 → ℝ) (hw : ∀ j : Fin 5, 0 < w j)
    (hsum : ∑ j : Fin 5, w j = 1)
    (hnd : ∃ j j' : Fin 5, r j ≠ r j') :
    (∃ j : Fin 5, r j < ∑ i : Fin 5, w i * r i) ∧
      (∃ j : Fin 5, (∑ i : Fin 5, w i * r i) < r j) := by sorry

end ZetaNine
