-- Prove2me | Theorems.Thm_section5_gaussian_grid_tail_230
-- name    : section5_gaussian_grid_tail_230
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:57.07563+00:00
-- url     : https://prove2.me/theorems/077f2a6c-3e45-47ce-a704-adf738cae167
-- title:
--   Gaussian mass outside the Hermite grid window (230)
-- statement:
--   Let $n,M\in\mathbb N$ with $M\ge1$, and let $X\sim N(0,I_n)$. For the grid radius $R_M=(M/2)\sqrt{4\pi/M}=\sqrt{\pi M}$,
--
--   $$\Pr\{\exists i:\ |X_i|\ge R_M\}\le2n\exp(-\pi M/2).$$
--
--   This bounds the Gaussian probability discarded by the finite spatial grid.
-- source:
--   Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1 and Appendix D, Eq. (230). Formalization: Solutions/Section5GaussianTail.lean, lines 155–160.

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
import Theorems.Thm_section5_gaussian_cube_tail
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Aux_w_53_hermite QuantumLTF.Example

theorem section5_gaussian_grid_tail_230 (n M : ℕ) (hM : 0 < M) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
      {x : Fin n → ℝ | ∃ i, gridRadius M ≤ |x i|} ≤
        2*n*Real.exp (-Real.pi*M/2) := by sorry
