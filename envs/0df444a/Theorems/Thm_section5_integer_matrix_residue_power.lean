-- Prove2me | Theorems.Thm_section5_integer_matrix_residue_power
-- name    : section5_integer_matrix_residue_power
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:53:31.844077+00:00
-- url     : https://prove2.me/theorems/d1327f55-837e-4c2a-9e2c-250a57a0304e
-- title:
--   Reduction modulo a power of two commutes with matrix powers
-- statement:
--   Let A be a complex integer n×n matrix and w,k natural numbers. Reducing each real and imaginary entry modulo 2^w commutes with taking the k-th matrix power: $$\operatorname{res}_{2^w}(A^k)=\operatorname{res}_{2^w}(A)^k.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ModularMatrixPowers.lean, lines 40–41.

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
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5ModularMatrixPowers
import Mathlib
set_option autoImplicit false
open QAlgorithms Thm49Primitives

theorem section5_integer_matrix_residue_power {n : ℕ} (A : Section5IntegerMatrix n) (w k : ℕ) :
    (A.power k).residue w=(A.residue w).power k := by sorry
