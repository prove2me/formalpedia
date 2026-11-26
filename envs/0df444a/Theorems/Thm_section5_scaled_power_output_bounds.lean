-- Prove2me | Theorems.Thm_section5_scaled_power_output_bounds
-- name    : section5_scaled_power_output_bounds
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:54.9979+00:00
-- url     : https://prove2.me/theorems/cec3ec4c-8f0a-5272-b538-88f678ccc279
-- title:
--   Lower and upper bounds for a scaled real output component
-- statement:
--   Let $n\ge1$, $y\in\mathbb C^n$, and $t\ge0$ be an integer. Suppose $2^{-t}\le2n\|y\|$ and $\|y\|\le2^t$. Choose $s=\operatorname{Re}y$ when $\|\operatorname{Im}y\|\le\|\operatorname{Re}y\|$, and otherwise choose $s=\operatorname{Im}y$. Set $r=2^{-t}s$. Then
--
--   $$
--   \frac1{3n4^t}\le\|r\|\le1.
--   $$
--
--   This supplies a positive magnitude bound and a unit-scale upper bound for fixed-point output preparation.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; this citation does not assert that the paper states the auxiliary result verbatim. Exact source: Solutions/Section5PowerOutputPrecision.lean, section5_scaled_power_output_bounds, lines 79–104.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5QuantizedReconstruction
import Mathlib
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_scaled_power_output_bounds {n : ℕ} (hn : 1 ≤ n)
    (y : EuclideanSpace ℂ (Fin n)) (t : ℕ)
    (hlo : (1/2:ℝ)^t ≤ 2*n*‖y‖) (hhi : ‖y‖ ≤ (2:ℝ)^t) :
    let r := ((2:ℝ)^t)⁻¹ • section5_larger_real_part y
    1/(3*n*(4:ℝ)^t) ≤ ‖r‖ ∧ ‖r‖ ≤ 1 := by sorry
