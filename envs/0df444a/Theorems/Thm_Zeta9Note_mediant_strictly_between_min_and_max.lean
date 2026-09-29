-- Prove2me | Theorems.Thm_Zeta9Note_mediant_strictly_between_min_and_max
-- name    : Zeta9Note.mediant_strictly_between_min_and_max
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T07:31:14.87922+00:00
-- url     : https://prove2.me/theorems/342c6ec7-23cc-49d5-bacb-eb9b427eb57c
-- title:
--   The weighted mediant lies strictly between the extreme ratios
-- statement:
--   Let w and b be strictly positive five-tuples and a an arbitrary five-tuple. If the ratios a_j / b_j are not all equal, then the ratio of the weighted sums (Σ w_i a_i) / (Σ w_i b_i) is strictly larger than the least of the ratios a_j / b_j and strictly smaller than the largest.
-- source:
--   Abstract layer distilled from the v0.1 research note (Zenodo 10.5281/zenodo.22951155); statement and proof in formalization/Zeta9Note.lean.

import Mathlib

namespace Zeta9Note

theorem mediant_strictly_between_min_and_max
    (w a b : Fin 5 → ℝ)
    (hw : ∀ j : Fin 5, 0 < w j)
    (hb : ∀ j : Fin 5, 0 < b j)
    (hnd : ∃ j j' : Fin 5, a j / b j ≠ a j' / b j') :
    (∃ j : Fin 5,
        a j / b j < (∑ i : Fin 5, w i * a i) / (∑ i : Fin 5, w i * b i)) ∧
      (∃ j : Fin 5,
        (∑ i : Fin 5, w i * a i) / (∑ i : Fin 5, w i * b i) < a j / b j) := by sorry

end Zeta9Note
