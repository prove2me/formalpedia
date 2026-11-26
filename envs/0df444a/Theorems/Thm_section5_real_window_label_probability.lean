-- Prove2me | Theorems.Thm_section5_real_window_label_probability
-- name    : section5_real_window_label_probability
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:13:18.308924+00:00
-- url     : https://prove2.me/theorems/9a261130-a59e-4f2e-bc98-44d695398d29
-- title:
--   Gaussian label error from a bounded signed coordinate window
-- statement:
--   Let $w\in\mathbb R^n$ be a unit vector, let $P,H$ be positive integers, and let $\delta>0$. Define $T(x)=\delta P\operatorname{sres}_H(\lfloor\lfloor x/\delta\rfloor/P\rfloor)$, where $\operatorname{sres}_H$ takes the representative modulo $2H$ in $[-H,H)$, and apply $T$ coordinatewise. For $f_w(x)=\operatorname{sgn}\langle w,x\rangle$ with sign $+1$ at zero,
--
--   $$\Pr_{X\sim N(0,I_n)}\{f_w(X)\ne f_w(T(X))\}\le2n e^{-(\delta HP)^2/2}+\frac{2\delta(P+1)\sqrt n}{\sqrt{2\pi}}.$$
--
--   This gives the label error incurred by keeping a bounded signed window of each Gaussian coordinate.
-- source:
--   Original real-window probability estimate for the Section 5 orientation subroutine, Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3. Formalization: Solutions/Section5RealWindow.lean, lines 48–58.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5RealWindow
import Mathlib
import Theorems.Thm_section5_coordinate_approximation_norm
import Theorems.Thm_section5_gaussian_cube_tail
import Theorems.Thm_section5_gaussian_inner_strip
import Theorems.Thm_section5_real_window_error
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example

theorem section5_real_window_label_probability {n : ℕ}
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1)
    (P H : ℤ) (hP : 0 < P) (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
      {x | ltf w 0 x ≠ ltf w 0 (section5_real_window_vec P H δ x)} ≤
        2*n*Real.exp (-(δ*H*P)^2/2)+
          2*((δ*(P+1))*Real.sqrt n)/Real.sqrt (2*Real.pi) := by sorry
