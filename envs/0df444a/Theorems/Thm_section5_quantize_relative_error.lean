-- Prove2me | Theorems.Thm_section5_quantize_relative_error
-- name    : section5_quantize_relative_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:00:53.957421+00:00
-- url     : https://prove2.me/theorems/8fae6694-4504-4bc8-8b18-774a2698c122
-- title:
--   Relative direction error after coordinatewise dyadic quantization
-- statement:
--   Let n≥1, 0<ε<1, b>0 and 2^f≥48n/(bε). Let r∈R^n satisfy |r_i|≤1 and ‖r‖≥b, and let Q_f round each coordinate downward to a multiple of 2^(−f). Then $$Q_f(r)\ne0,\qquad\left\|\frac{Q_f(r)}{\|Q_f(r)\|}-\frac r{\|r\|}\right\|\le\varepsilon/24.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5FixedPointQuantization.lean, lines 107–112.

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

theorem section5_quantize_relative_error {n : ℕ} (hn : 1 ≤ n) (f : ℕ)
    (ε b : ℝ) (hε : 0 < ε) (hε' : ε < 1) (hb : 0 < b)
    (hprec : 48*(n:ℝ)/(b*ε) ≤ (2:ℝ)^f)
    (r : EuclideanSpace ℝ (Fin n)) (hr : ∀ i, |r i| ≤ 1) (hnorm : b ≤ ‖r‖) :
    section5_quantize_vector f r ≠ 0 ∧
      ‖NormedSpace.normalize (section5_quantize_vector f r)-NormedSpace.normalize r‖ ≤ ε/24 := by sorry
