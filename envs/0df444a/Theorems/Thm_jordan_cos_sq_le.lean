-- Prove2me | Theorems.Thm_jordan_cos_sq_le
-- name    : jordan_cos_sq_le
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-09T11:57:07.012986+00:00
-- url     : https://prove2.me/theorems/7354aa41-8a8b-4816-a362-e9fe376c586e
-- statement:
--   Consequence of Jordan's inequality: cos^2(pi/(2d)) <= 1 - 1/d^2 for natural d >= 1. Equivalent to sin(pi/(2d)) >= 1/d. Proof: sin is concave on [0, pi/2] (Real.strictConcaveOn_sin or similar), so by the chord inequality sin(t) >= (2/pi) t for t in [0, pi/2]. At t = pi/(2d): sin(pi/(2d)) >= (2/pi)(pi/(2d)) = 1/d. Then cos^2 = 1 - sin^2 <= 1 - 1/d^2. Equality at d = 1.
-- source:
--   Nisan, Noam, and Mario Szegedy. "On the degree of Boolean functions as real polynomials." Computational Complexity 4.4 (1994): 301-313. (Bound used in Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.)

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic

theorem jordan_cos_sq_le (d : ℕ) (hd : 1 ≤ d) :
    Real.cos (Real.pi / (2 * (d : ℝ)))^2 ≤ 1 - 1/(d : ℝ)^2 := by sorry
