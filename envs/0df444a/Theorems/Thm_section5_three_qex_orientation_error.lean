-- Prove2me | Theorems.Thm_section5_three_qex_orientation_error
-- name    : section5_three_qex_orientation_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:41:50.520802+00:00
-- url     : https://prove2.me/theorems/1822f5ea-a2e3-44aa-951b-a477b214cdad
-- title:
--   Three independent QEX orientation votes have error at most $5/32$
-- statement:
--   Let $n\ge1$, $0<\varepsilon<1$, and $q\in\mathbb N$ satisfy $2^q\ge2^{30}n^2/\varepsilon^2$. Let $w,u\in\mathbb R^n$ be unit vectors, and let $b\in\{0,1\}$ satisfy $\|(-1)^b u-w\|\le\varepsilon/6$. Draw $Z_1,Z_2,Z_3$ independently with probability $p(z)$ proportional to $e^{-\|x_z\|^2/2}$ on the centered $n$-coordinate $q$-bit grid. Define an erroneous vote $E_b(z)$ by $f_w(x_z)\ne f_u(x_z)$ when $b=0$, and by equality when $b=1$, where $f_v=\operatorname{sgn}\langle v,\cdot\rangle$ with sign $+1$ at zero. Then
--
--   $$\Pr\{\text{at least two of }E_b(Z_1),E_b(Z_2),E_b(Z_3)\}\le\frac5{32}.$$
--
--   This gives the three-sample orientation amplification bound for either possible global sign.
-- source:
--   Original finite-QEX majority-vote auxiliary result for Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5. Formalization: Solutions/Section5OrientationAmplification.lean, lines 65–85. Gaussian disagreement dependency: kmehltretter82, accepted submission f5f65d6e-b702-475a-bc3e-8683c2844aa9 (Apache-2.0), credited in Solutions/Section5GaussianDisagreementFoundation.lean.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5OrientationAmplification
import Mathlib
import Theorems.Thm_section5_qex_negative_orientation_vote_quarter
import Theorems.Thm_section5_qex_orientation_vote_quarter
import Theorems.Thm_section5_three_independent_errors
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_three_qex_orientation_error (n q : ℕ) (hn : 1 ≤ n) (ε : ℝ)
    (hε : 0 < ε) (hε' : ε < 1)
    (hgrid : 1073741824*(n:ℝ)^2/ε^2 ≤ (2:ℝ)^q)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hu : ‖u‖=1)
    (flip : Bool) (hclose : ‖(if flip then -u else u)-w‖ ≤ ε/6) :
    open Classical in
    (∑ a : Qubits (n*q), ∑ b : Qubits (n*q), ∑ c : Qubits (n*q),
      if (section5_orientation_error w u flip a ∧ section5_orientation_error w u flip b) ∨
        (section5_orientation_error w u flip a ∧ section5_orientation_error w u flip c) ∨
        (section5_orientation_error w u flip b ∧ section5_orientation_error w u flip c)
      then section5_qex_distribution n q a*section5_qex_distribution n q b*
        section5_qex_distribution n q c else 0) ≤ 5/32 := by sorry
