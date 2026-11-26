-- Prove2me | Theorems.Thm_section5_quantize_normalized_error
-- name    : section5_quantize_normalized_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:00:31.853645+00:00
-- url     : https://prove2.me/theorems/7c1adc2e-a825-5bdd-a9c9-a2d6d91cf650
-- title:
--   Direction error after fixed-point quantization
-- statement:
--   Let n≥1, 0<ε<1 and 2^f≥128n/ε. Let r∈R^n satisfy |r_i|≤1 and ‖r‖≥2/3. For coordinatewise downward dyadic quantization Q_f at step 2^(−f), $$Q_f(r)\ne0,\qquad\left\|\frac{Q_f(r)}{\|Q_f(r)\|}-\frac r{\|r\|}\right\|\le\varepsilon/24.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5FixedPointQuantization.lean, lines 79–83.

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
import Definitions.Def_Section5Verified_Section5FixedPointQuantization
import Mathlib
import Theorems.Thm_section5_coordinate_approximation_norm
import Theorems.Thm_section5_normalize_perturbation
import Theorems.Thm_section5_quantize_decode
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_quantize_normalized_error {n : ℕ} (hn : 1 ≤ n) (f : ℕ)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (hprec : 128*(n:ℝ)/ε ≤ (2:ℝ)^f)
    (r : EuclideanSpace ℝ (Fin n)) (hr : ∀ i, |r i| ≤ 1) (hnorm : 2/3 ≤ ‖r‖) :
    section5_quantize_vector f r ≠ 0 ∧
      ‖NormedSpace.normalize (section5_quantize_vector f r)-NormedSpace.normalize r‖ ≤ ε/24 := by sorry
