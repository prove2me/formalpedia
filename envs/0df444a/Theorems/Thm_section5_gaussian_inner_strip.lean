-- Prove2me | Theorems.Thm_section5_gaussian_inner_strip
-- name    : section5_gaussian_inner_strip
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:22:10.710066+00:00
-- url     : https://prove2.me/theorems/3326919b-f1ba-4ae3-bb5f-f2a842c3715b
-- title:
--   Gaussian mass of a strip perpendicular to a unit vector
-- statement:
--   Let w∈R^n satisfy ‖w‖=1, let t≥0 and let X be standard Gaussian in R^n. Then $$\Pr[|\langle w,X\rangle|\le t]\le2t/\sqrt{2\pi}.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5GaussianRounding.lean, lines 83–86.

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example

theorem section5_gaussian_inner_strip {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (hw : ‖w‖ = 1) (t : ℝ) (ht : 0 ≤ t) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real {x | |inner ℝ w x| ≤ t} ≤
      2*t/Real.sqrt (2*Real.pi) := by sorry
