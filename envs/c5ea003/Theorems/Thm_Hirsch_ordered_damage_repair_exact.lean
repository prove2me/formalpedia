-- Prove2me | Theorems.Thm_Hirsch_ordered_damage_repair_exact
-- name    : Hirsch.ordered_damage_repair_exact
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-09T14:01:45.066109+00:00
-- url     : https://prove2.me/theorems/238cbea9-9f9a-454d-93e5-94344960261e
-- title:
--   Exact ordered damage repair with surviving gaps
-- statement:
--   Marked ordered damage intervals may contain destroyed steps; only the gaps between them must survive. Replacing each damaged interval through its certified extreme face gives exact padded budget L minus removed interval length plus the sum of replacement face budgets.
-- source:
--   Verified Lean theorem from jjoshua2/prove2me-work PR #40.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

theorem Hirsch.ordered_damage_repair_exact
    {d m L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (s t B : Fin m → ℕ)
    (F : Fin m → Set (EuclideanSpace ℝ (Fin d)))
    (hst : ∀ i, s i ≤ t i) (htL : ∀ i, t i ≤ L)
    (horder : ∀ i j, i < j → t i ≤ s j)
    (hF : ∀ i, IsExtreme ℝ P (F i))
    (hD : ∀ i, DiamLE (F i) (B i))
    (hends : ∀ i, w (s i) ∈ extremePoints ℝ P ∧ w (t i) ∈ extremePoints ℝ P)
    (hin : ∀ i, w (s i) ∈ F i ∧ w (t i) ∈ F i)
    (hsurvive : ∀ j, j < L → (∀ i, j < s i ∨ t i ≤ j) →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w 0 ∧ q (L - (∑ i, (t i - s i)) + (∑ i, B i)) = w L ∧
      ∀ j < L - (∑ i, (t i - s i)) + (∑ i, B i),
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by sorry
