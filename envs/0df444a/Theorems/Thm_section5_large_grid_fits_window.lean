-- Prove2me | Theorems.Thm_section5_large_grid_fits_window
-- name    : section5_large_grid_fits_window
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:09:02.596248+00:00
-- url     : https://prove2.me/theorems/f79fb8fc-c9f6-5aaf-8b5f-6413c7792ffb
-- title:
--   A large grid contains the selected middle window
-- statement:
--   For natural n≥1 and q with 2^q≥2^40n², let B=⌈log₂(65536n)⌉. The chosen window fits within q bits: $$2B+6\le q.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5BoundedWindow.lean, lines 74–76.

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
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5BoundedWindow
import Mathlib
import Theorems.Thm_section5_window_precision_bounds
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_large_grid_fits_window (n q : ℕ) (hn : 1 ≤ n)
    (hM : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q) :
    2*section5_window_precision n+6 ≤ q := by sorry
