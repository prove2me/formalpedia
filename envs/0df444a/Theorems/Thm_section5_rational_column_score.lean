-- Prove2me | Theorems.Thm_section5_rational_column_score
-- name    : section5_rational_column_score
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:54:51.131885+00:00
-- url     : https://prove2.me/theorems/d211fe22-6cab-5a2f-a9fa-d0cd95ab6bdd
-- title:
--   Rational column score equals the squared complex column norm
-- statement:
--   Let $A$ be an $n\times n$ matrix with rational real and imaginary parts, represented as a complex linear operator on $\mathbb C^n$. Define $s_j=\sum_i((\operatorname{Re}A_{ij})^2+(\operatorname{Im}A_{ij})^2)\in\mathbb Q$, and let $e_j$ be the standard coordinate vector. Then
--
--   $$
--   \|Ae_j\|^2=s_j,
--   $$
--
--   where the rational score is viewed as a real number.
--
--   This makes exact rational score comparisons available for selecting a complex matrix column.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; this citation does not assert that the paper states the auxiliary result verbatim. Exact source: Solutions/Section5RationalReconstruction.lean, section5_rational_column_score, lines 107–120.

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
import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Definitions.Def_Section5Verified_Section5RationalReconstruction
import Mathlib
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_rational_column_score {n : ℕ} (A : Section5RationalMatrix n) (j : Fin n) :
    ‖A.operator (section5_coordinate_ket j)‖^2=(A.columnScore j:ℝ) := by sorry
