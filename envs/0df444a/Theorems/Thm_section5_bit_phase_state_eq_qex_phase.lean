-- Prove2me | Theorems.Thm_section5_bit_phase_state_eq_qex_phase
-- name    : section5_bit_phase_state_eq_qex_phase
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:01:03.673883+00:00
-- url     : https://prove2.me/theorems/a2632743-82ca-478c-a56b-abcb542d23db
-- title:
--   The bit-grid phase state equals the QEX phase amplitude
-- statement:
--   Let $w\in\mathbb R^n$, let $q\ge1$, and let $z=(z_1,\ldots,z_n)$ be $n$ registers of $q$ bits. Write $\operatorname{flat}(z)$ for their concatenation, $x_y$ for the centered Gaussian grid point of a flat string $y$, and $p(y)=e^{-\|x_y\|^2/2}/\sum_v e^{-\|x_v\|^2/2}$. Let $\Psi_{w,q}^{\mathrm{bit}}$ be the normalized finite sampled threshold phase state reindexed by these bit registers, and let $f_w(x)=\operatorname{sgn}\langle w,x\rangle$, with sign $+1$ at zero. Then
--
--   $$\Psi_{w,q}^{\mathrm{bit}}(z)=f_w(x_{\operatorname{flat}(z)})\sqrt{p(\operatorname{flat}(z))}.$$
--
--   This matches the analytic finite-grid phase state to the phase branch associated with the QEX encoding.
-- source:
--   Original QEX/grid identification for Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1. Formalization: Solutions/Section5GridPhaseMatchesQEX.lean, lines 119–127. Public QEX definition: Definitions/Def_QuantumLTF_Example_qex.lean.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5ExamplePhase
import Definitions.Def_Section5Verified_Section5FiniteCoefficientTransfer
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Definitions.Def_Section5Verified_Section5PhysicalHermiteGrid
import Mathlib
import Theorems.Thm_section5_grid_exp_sum
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership Aux_w_53_hermite

theorem section5_bit_phase_state_eq_qex_phase {n q : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (hq : 0 < q) (z : Fin n → Qubits q) :
    section5_bit_phase_state w q z =
      (ltf w 0 (gridPoint (flatReg n q z)) : ℂ)*section5_grid_amplitude (flatReg n q z) := by sorry
