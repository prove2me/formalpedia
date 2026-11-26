-- Prove2me | Theorems.Thm_section5_gaussian_cube_tail
-- name    : section5_gaussian_cube_tail
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-26T19:39:20.132372+00:00
-- url     : https://prove2.me/theorems/9092696f-077c-4f00-9afb-c75eacd54ffa
-- title:
--   Gaussian probability outside a coordinate cube
-- statement:
--   Let $n\ge0$, $L\ge0$, and let $X_1,\ldots,X_n$ be independent standard real Gaussian variables. Then
--
--   $$
--   \Pr\{\exists i:\ |X_i|\ge L\}\le2n e^{-L^2/2}.
--   $$
--
--   This bounds the probability outside an axis-aligned Gaussian cube.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; not asserted to be a separately numbered result of the paper. Exact local source: Solutions/Section5GaussianTail.lean, section5_gaussian_cube_tail, lines 126–146.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Mathlib
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Aux_w_53_hermite QuantumLTF.Example

theorem section5_gaussian_cube_tail (n : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
      {x : Fin n → ℝ | ∃ i, L ≤ |x i|} ≤ 2*n*Real.exp (-L^2/2) := by sorry
