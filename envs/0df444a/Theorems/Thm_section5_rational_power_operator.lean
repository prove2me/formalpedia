-- Prove2me | Theorems.Thm_section5_rational_power_operator
-- name    : section5_rational_power_operator
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:02.986313+00:00
-- url     : https://prove2.me/theorems/4350dd54-d3e3-40fd-829d-f5b755daea4a
-- title:
--   Rational matrix powers agree with operator powers
-- statement:
--   Let A be an n×n matrix with rational real and imaginary entries and let k be natural. The operator associated to its exact rational matrix power is the power of the associated complex Euclidean operator: $$\operatorname{op}(A^k)=\operatorname{op}(A)^k.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5RationalReconstruction.lean, lines 68–69.

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
import Definitions.Def_Section5Verified_Section5RationalReconstruction
import Mathlib
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_rational_power_operator {n : ℕ} (A : Section5RationalMatrix n) (k : ℕ) :
    (A.power k).operator=A.operator^k := by sorry
