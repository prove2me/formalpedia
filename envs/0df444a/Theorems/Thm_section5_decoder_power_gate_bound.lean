-- Prove2me | Theorems.Thm_section5_decoder_power_gate_bound
-- name    : section5_decoder_power_gate_bound
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:53:22.419147+00:00
-- url     : https://prove2.me/theorems/cd75eea6-efa6-41bf-930c-e52302c7bb21
-- title:
--   Polynomial bound on decoder power arithmetic
-- statement:
--   Let n≥1 and 0<ε<1, and let k,b be the explicit decoder iteration count and integer width. The fixed-width matrix-power circuit's gate bound satisfies $$88n^3(b+1)^3k\le10^{25}(n/\varepsilon)^{13}.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5DyadicDecoderParameters.lean, lines 109–113.

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
import Definitions.Def_Section5Verified_Section5DyadicDecoderParameters
import Mathlib
import Theorems.Thm_section5_decoder_parameters_polynomial
set_option autoImplicit false

theorem section5_decoder_power_gate_bound (n : ℕ) (hn : 1 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    ((88*n^3*(section5_decoder_integer_width n ε+1)^3)*
      section5_decoder_iterations n ε:ℕ) ≤
        (10:ℝ)^25*((n:ℝ)/ε)^13 := by sorry
