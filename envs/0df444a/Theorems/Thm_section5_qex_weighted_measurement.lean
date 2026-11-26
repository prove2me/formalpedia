-- Prove2me | Theorems.Thm_section5_qex_weighted_measurement
-- name    : section5_qex_weighted_measurement
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:54:34.038449+00:00
-- url     : https://prove2.me/theorems/609ed0bb-a777-41c3-b13a-d69ce921c6e7
-- title:
--   Exact weighted measurement identity for one finite QEX state
-- statement:
--   Let w∈R^n, q natural and G any real function on the n q spatial bits and one label bit. Let p(x) be the normalized finite Gaussian grid weight and L_w(x) append the bit [ltf_{w,0}(grid(x))=−1]. Measuring the finite QEX state gives $$\sum_z|\operatorname{QEX}_w(z)|^2G(z)=\sum_xp(x)G(L_w(x)).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5QEXMeasurementLaw.lean, lines 25–29.

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
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_qex_weighted_measurement {n q : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (G : Qubits (n*q+1) → ℝ) :
    (∑ z : Qubits (n*q+1), prob (qexKet (q:=q) w) z*G z)=
      ∑ x : Qubits (n*q), section5_qex_distribution n q x*
        G (Fin.snoc x (decide (ltf w 0 (gridPoint x)= -1))) := by sorry
