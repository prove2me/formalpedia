-- Prove2me | Theorems.Thm_section5_rational_real_candidate
-- name    : section5_rational_real_candidate
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:12.974564+00:00
-- url     : https://prove2.me/theorems/111bf9a2-9a56-4833-9419-07894d7b346e
-- title:
--   Exact rational candidate agrees with the larger real column part
-- statement:
--   Let A be an n×n complex matrix with rational real and imaginary entries and n≥1. Select j by the source's exact rational maximum-column-score rule, and select the larger squared-norm real or imaginary part of column j, breaking ties toward the real part. The resulting rational candidate r agrees after coercion to R^n with the larger real part R of its complex operator column: $$r=R(\operatorname{op}(A)e_j).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5RationalReconstruction.lean, lines 154–156.

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
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Definitions.Def_Section5Verified_Section5QuantizedReconstruction
import Definitions.Def_Section5Verified_Section5RationalReconstruction
import Mathlib
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_rational_real_candidate {n : ℕ} (A : Section5RationalMatrix n) (hn : 1 ≤ n) :
    WithLp.toLp 2 (fun i => (A.realCandidate hn i:ℝ))=
      section5_larger_real_part (A.operator (section5_coordinate_ket (A.bestColumn hn))) := by sorry
