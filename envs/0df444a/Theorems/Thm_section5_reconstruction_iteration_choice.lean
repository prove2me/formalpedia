-- Prove2me | Theorems.Thm_section5_reconstruction_iteration_choice
-- name    : section5_reconstruction_iteration_choice
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:25.073785+00:00
-- url     : https://prove2.me/theorems/a81480d6-9bef-5601-985d-18ae4e033335
-- title:
--   An explicit sufficient matrix-power iteration count
-- statement:
--   Let n be natural, ε>0 and let k be the binary-precision function at 400n/ε as defined in the source. Then $$400n/\varepsilon\le2^{k+1},\qquad k<400n/\varepsilon+1.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ReconstructionPrecision.lean, lines 21–23.

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
import Definitions.Def_Section5Verified_Section5ReconstructionPrecision
import Mathlib
set_option autoImplicit false

theorem section5_reconstruction_iteration_choice (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    400*(n:ℝ)/ε ≤ (2:ℝ)^(section5_binary_precision (400*n/ε)+1) ∧
      (section5_binary_precision (400*n/ε):ℝ) < 400*n/ε+1 := by sorry
