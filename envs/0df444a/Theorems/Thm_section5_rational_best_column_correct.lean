-- Prove2me | Theorems.Thm_section5_rational_best_column_correct
-- name    : section5_rational_best_column_correct
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:00:03.671785+00:00
-- url     : https://prove2.me/theorems/68cdfedf-9acc-42d6-b502-a099fdeb579d
-- title:
--   Exact rational selection maximizes column norm
-- statement:
--   Let A have rational real and imaginary entries and n≥1. Let j be its computable best-column index, selected by comparing exact rational squared column norms. Then $$\forall i:\quad\|\operatorname{op}(A)e_i\|\le\|\operatorname{op}(A)e_j\|.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5RationalReconstruction.lean, lines 122–124.

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
import Theorems.Thm_section5_rational_column_score
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_rational_best_column_correct {n : ℕ} (A : Section5RationalMatrix n) (hn : 1 ≤ n) :
    ∀ i, ‖A.operator (section5_coordinate_ket i)‖ ≤
      ‖A.operator (section5_coordinate_ket (A.bestColumn hn))‖ := by sorry
