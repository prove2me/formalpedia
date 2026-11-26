-- Prove2me | Theorems.Thm_section5_real_window_error
-- name    : section5_real_window_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:10:46.387797+00:00
-- url     : https://prove2.me/theorems/5bc410e3-2cf3-5726-ba4c-2066a68d6053
-- title:
--   Approximation error of a bounded signed real window
-- statement:
--   Let $P,H$ be positive integers and let $\delta>0$. For an integer $u$, define $\rho_H(u)$ as its unique representative modulo $2H$ in $[-H,H)$. Define $W_{P,H}(z)=P\rho_H(\lfloor z/P\rfloor)$ for integers $z$, and $R(x)=\delta W_{P,H}(\lfloor x/\delta\rfloor)$. If $x\in\mathbb R$ satisfies $|x|<\delta HP$, then
--
--   $$
--   |x-R(x)|<\delta(P+1).
--   $$
--
--   This bounds the approximation error from lattice rounding and signed-window truncation within the represented interval.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; this citation does not assert that the paper states the auxiliary result verbatim. Exact source: Solutions/Section5RealWindow.lean, section5_real_window_error, lines 14–42.

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
import Definitions.Def_Section5Verified_Section5SignedWindow
import Mathlib
import Theorems.Thm_section5_window_truncate_error
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example

theorem section5_real_window_error (P H : ℤ) (hP : 0 < P) (hH : 0 < H)
    (δ : ℝ) (hδ : 0 < δ) (x : ℝ) (hx : |x| < δ*H*P) :
    |x-section5_real_window P H δ x| < δ*(P+1) := by sorry
