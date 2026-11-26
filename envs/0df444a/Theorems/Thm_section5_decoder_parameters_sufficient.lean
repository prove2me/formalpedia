-- Prove2me | Theorems.Thm_section5_decoder_parameters_sufficient
-- name    : section5_decoder_parameters_sufficient
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:46:25.639865+00:00
-- url     : https://prove2.me/theorems/89de3985-6c77-5d38-9ce3-092d99ed9508
-- title:
--   Sufficiency of explicit decoder parameters
-- statement:
--   Let n be natural and ε>0. Let β(x)=clog₂(⌈x⌉₊), k=β(800n/ε), f=2(k+1)+β(144n²/ε), c=β(n), and b=(k+1)(f+c+3)+2. These parameters satisfy $$800n/\varepsilon\le2^{k+1},\quad144n^24^{k+1}/\varepsilon\le2^f,\quad n\le2^c,\quad f\le(f+1)(k+1),\quad(f+1)(k+1)+2\le b+1,\quad(k+1)(f+c+2)<b.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5DyadicDecoderParameters.lean, lines 19–27.

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
import Definitions.Def_Section5Verified_Section5ReconstructionPrecision
import Mathlib
set_option autoImplicit false

theorem section5_decoder_parameters_sufficient (n : ℕ) (ε : ℝ) (_hε : 0 < ε) :
    let k := section5_decoder_iterations n ε
    let f := section5_decoder_fraction_bits n ε
    let c := section5_binary_precision n
    let b := section5_decoder_integer_width n ε
    800*(n:ℝ)/ε ≤ (2:ℝ)^(k+1) ∧
      144*(n:ℝ)^2*(4:ℝ)^(k+1)/ε ≤ (2:ℝ)^f ∧
      n ≤ 2^c ∧ f ≤ (f+1)*(k+1) ∧
      (f+1)*(k+1)+2 ≤ b+1 ∧ (k+1)*(f+1+c+1) < b := by sorry
