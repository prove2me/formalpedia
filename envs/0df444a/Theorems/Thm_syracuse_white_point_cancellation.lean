-- Prove2me | Theorems.Thm_syracuse_white_point_cancellation
-- name    : syracuse_white_point_cancellation
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-09T09:01:19.321983+00:00
-- url     : https://prove2.me/theorems/7a73f14d-d576-4565-acfb-c53e02e4be01
-- title:
--   White-point cancellation for the positive Syracuse pair
-- statement:
--   Let N=3^n, let ξ be a unit modulo N, let 1≤j with 2j≤n, and let l be an integer. Put P=ξ·3^(2j−2)·2^(1−l) in Z/NZ, let u be the centered representative of P.val/N in (−1/2,1/2], and write e_N(t)=exp(2πit/N). Let A1,A2 be independent positive geometric variables with P(Ai=k)=2^(-k) for k≥1. If 0<ε<1/100 and ε<|u|, then
--
--   | E[ e_N(−2^(-1) P (2^A2+3)) | A1+A2=3 ] | ≤ exp(−ε^3).
--
--   The conditioning event has probability 1/4 and its two atoms, (A1,A2)=(1,2) and (2,1), each have mass 1/8. Their source factors are 7 and 5. In the pair reduction, the exact phase −2^(-1)P gives e_N(−P), because 2·(−2^(-1)P)=−P. The remaining normalized two-point average is controlled by the centered cosine estimate.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, arXiv:1909.03562v7, Section 7.1, especially (7.7)--(7.10) and Lemma 7.2, https://arxiv.org/html/1909.03562v7. The formal statement is only the deterministic white-point cancellation step; it does not assert Proposition 1.14 or any distribution theorem.

import Mathlib
import Definitions.Def_syracuseDyadicPhase
import Definitions.Def_positivePairSumThree
import Definitions.Def_positivePairCharacterAverage
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators Classical

theorem syracuse_white_point_cancellation (n : ℕ) (hn : 1 ≤ n) (ξ : ZMod (3 ^ n)) (hξ : IsUnit ξ) (j : ℕ) (hj : 1 ≤ j) (hjn : 2 * j ≤ n) (l : ℤ) (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < 1 / 100) (hwhite : ε < |centeredPhase (((syracuseDyadicPhase n ξ j l).val : ℝ) / (3 ^ n : ℝ))|) : ‖syracuseWhitePointAverage n ξ j l‖ ≤ Real.exp (-ε ^ 3) := by sorry
