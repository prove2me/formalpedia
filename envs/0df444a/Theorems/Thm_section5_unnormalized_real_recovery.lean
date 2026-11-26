-- Prove2me | Theorems.Thm_section5_unnormalized_real_recovery
-- name    : section5_unnormalized_real_recovery
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:02:52.798937+00:00
-- url     : https://prove2.me/theorems/d15ad496-9c6f-43b5-afbe-ae7609745edd
-- title:
--   Real-direction recovery from an unnormalized complex vector
-- statement:
--   Let y∈C^n be nonzero, w∈R^n unit, ζ complex and 0<ε<1. Assume ‖y/‖y‖−ζw‖≤ε/24. Let r be the larger-norm real or imaginary part of y. Then $$r\ne0,\qquad\min\{\|r/\|r\|-w\|,\|r/\|r\|+w\|\}\le\varepsilon/6.$$ No separate modulus condition on ζ is assumed.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5UnnormalizedRecovery.lean, lines 31–38.

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
import Definitions.Def_Section5Verified_Section5QuantizedReconstruction
import Mathlib
import Theorems.Thm_section5_real_direction_recovery
set_option autoImplicit false

theorem section5_unnormalized_real_recovery {n : ℕ}
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ≠ 0)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1)
    (ζ : ℂ) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hclose : ‖NormedSpace.normalize y-ζ • section5_complexify w‖ ≤ ε/24) :
    section5_larger_real_part y ≠ 0 ∧
      (‖NormedSpace.normalize (section5_larger_real_part y)-w‖ ≤ ε/6 ∨
        ‖NormedSpace.normalize (section5_larger_real_part y)+w‖ ≤ ε/6) := by sorry
