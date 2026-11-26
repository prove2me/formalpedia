-- Prove2me | Theorems.Thm_section5_qex_oracle_probEvent
-- name    : section5_qex_oracle_probEvent
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:58:34.90091+00:00
-- url     : https://prove2.me/theorems/6aae25ae-6361-58c3-9eb7-fabfd1f8f1d0
-- title:
--   Event probabilities of a supplied QEX oracle
-- statement:
--   Let w∈R^n and let U satisfy the finite QEX oracle specification, including preparation of the published QEX state from the all-zero input. For any decidable event P, let p(x) be the finite Gaussian grid weight and L_w(x) append the true negative-label bit. Then $$\operatorname{probEvent}(U|0\rangle,P)=\sum_x\mathbf1_{P(L_w(x))}p(x).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5QEXMeasurementLaw.lean, lines 49–54.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_probMixed
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5OrientationAmplification
import Mathlib
import Theorems.Thm_section5_qex_weighted_measurement
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_qex_oracle_probEvent {n q : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (U : Matrix (Qubits (n*q+1)) (Qubits (n*q+1)) ℂ) (hU : IsQEX (q:=q) w U)
    (P : Qubits (n*q+1) → Prop) [DecidablePred P] :
    probEvent (act U (zeroKet (n*q+1))) P=
      ∑ x : Qubits (n*q), if P (Fin.snoc x (decide (ltf w 0 (gridPoint x)= -1))) then
        section5_qex_distribution n q x else 0 := by sorry
