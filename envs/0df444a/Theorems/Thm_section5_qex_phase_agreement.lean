-- Prove2me | Theorems.Thm_section5_qex_phase_agreement
-- name    : section5_qex_phase_agreement
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:03:52.565781+00:00
-- url     : https://prove2.me/theorems/f33f669e-20e5-4cde-9510-8bfce027e711
-- title:
--   Squared sum of QEX phase states equals four times label agreement
-- statement:
--   Let n,q be natural and w,u∈R^n arbitrary. Let Ψ_w,Ψ_u be normalized finite Gaussian spatial states with their respective homogeneous-threshold phases on the same grid, and let p(z) be normalized grid weights. Then $$\|\Psi_w+\Psi_u\|_2^2=4\sum_zp(z)\mathbf1_{\operatorname{ltf}_{w,0}(\operatorname{grid}(z))=\operatorname{ltf}_{u,0}(\operatorname{grid}(z))}.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5SignedOrientationVote.lean, lines 65–69.

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
import Definitions.Def_Section5Verified_Section5DiscretizationLemma
import Mathlib
import Theorems.Thm_section5_phase_amplitude_norm
import Theorems.Thm_section5_qex_phase_disagreement
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_qex_phase_agreement {n q : ℕ} (w u : EuclideanSpace ℝ (Fin n)) :
    ‖section5_qex_phase_input w q+section5_qex_phase_input u q‖^2 =
      4*∑ z : Qubits (n*q),
        if ltf w 0 (gridPoint z) = ltf u 0 (gridPoint z) then
          gridWeight z/(∑ x : Qubits (n*q), gridWeight x) else 0 := by sorry
