-- Prove2me | Theorems.Thm_section5_uniform_power_output_quantization
-- name    : section5_uniform_power_output_quantization
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:07:57.168832+00:00
-- url     : https://prove2.me/theorems/3afbb660-fe5c-4209-9e60-8773f31fa9cd
-- title:
--   Uniform quantization precision for powered-column output
-- statement:
--   Let n≥1, y∈C^n and t,f natural. Suppose 2^(−t)≤2n‖y‖≤2n·2^t, 0<ε<1 and 2^f≥144n²4^t/ε. Put r=2^(−t) times the larger-norm real or imaginary part of y, and let Q_f be downward dyadic quantization. Then $$Q_f(r)\ne0,\qquad\|Q_f(r)/\|Q_f(r)\|-r/\|r\|\|\le\varepsilon/24.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5PowerOutputPrecision.lean, lines 106–113.

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
import Definitions.Def_Section5Verified_Section5QuantizedReconstruction
import Mathlib
import Theorems.Thm_section5_quantize_relative_error
import Theorems.Thm_section5_scaled_power_output_bounds
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_uniform_power_output_quantization {n : ℕ} (hn : 1 ≤ n)
    (y : EuclideanSpace ℂ (Fin n)) (t f : ℕ)
    (hlo : (1/2:ℝ)^t ≤ 2*n*‖y‖) (hhi : ‖y‖ ≤ (2:ℝ)^t)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hprec : 144*(n:ℝ)^2*(4:ℝ)^t/ε ≤ (2:ℝ)^f) :
    let r := ((2:ℝ)^t)⁻¹ • section5_larger_real_part y
    section5_quantize_vector f r ≠ 0 ∧
      ‖NormedSpace.normalize (section5_quantize_vector f r)-NormedSpace.normalize r‖ ≤ ε/24 := by sorry
