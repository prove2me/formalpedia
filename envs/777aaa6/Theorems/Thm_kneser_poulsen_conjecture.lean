-- Prove2me | Theorems.Thm_kneser_poulsen_conjecture
-- name    : kneser_poulsen_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:29:50.88115+00:00
-- url     : https://prove2.me/theorems/78b22ff6-c77c-4a2d-9573-88ab53a7af86
-- statement:
--   The Kneser–Poulsen conjecture (1955): If a finite set of balls in ℝᵈ is rearranged so that the distance between each pair of centers does not increase, then the volume of the union does not increase. Proved in ℝ² (Bezdek–Connelly 2002). Open in dimensions d ≥ 3.
-- source:
--   https://en.wikipedia.org/wiki/Kneser%E2%80%93Poulsen_conjecture

import Mathlib

import Mathlib

theorem kneser_poulsen_conjecture (n d : ℕ) (hd : 1 ≤ d)
    (centers : Fin n → EuclideanSpace ℝ (Fin d))
    (centers' : Fin n → EuclideanSpace ℝ (Fin d))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hcontract : ∀ i j : Fin n, dist (centers' i) (centers' j) ≤ dist (centers i) (centers j)) :
    MeasureTheory.volume (⋃ i, Metric.ball (centers' i) (r i)) ≤
    MeasureTheory.volume (⋃ i, Metric.ball (centers i) (r i)) := by
  sorry
