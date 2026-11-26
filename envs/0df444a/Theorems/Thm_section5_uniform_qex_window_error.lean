-- Prove2me | Theorems.Thm_section5_uniform_qex_window_error
-- name    : section5_uniform_qex_window_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:43:00.842485+00:00
-- url     : https://prove2.me/theorems/4f78b6d8-2d3e-505f-8e3b-e56654957505
-- title:
--   Uniform middle-window label error
-- statement:
--   Let n≥1, M=2^q≥2^40n² and u be a real unit vector. Put B=⌈log₂(65536n)⌉, P=2^(⌊q/2⌋−B), H=2^(2B+1), and δ=√(4π/M). For normalized Gaussian grid Z and the centered real-window map W with these parameters, $$\Pr[\operatorname{sgn}\langle u,Z\rangle\ne\operatorname{sgn}\langle u,WZ\rangle]\le1/32.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5BoundedWindow.lean, lines 87–95.

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
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5RealWindow
import Mathlib
import Theorems.Thm_section5_finite_window_error_budget
import Theorems.Thm_section5_large_grid_fits_window
import Theorems.Thm_section5_middle_window_scales
import Theorems.Thm_section5_qex_window_label_error
import Theorems.Thm_section5_window_precision_bounds
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

open Classical in
theorem section5_uniform_qex_window_error (n q : ℕ) (hn : 1 ≤ n)
    (hM : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖=1) :
    let B := section5_window_precision n
    (∑ z : Qubits (n*q),
      if ltf u 0 (gridPoint z) ≠ ltf u 0
          (section5_real_window_vec ((2:ℤ)^(q/2-B)) ((2:ℤ)^(2*B+1))
            (gridSpacing (2^q)) (gridPoint z)) then
        gridWeight z/(∑ y : Qubits (n*q), gridWeight y) else 0) ≤ 1/32 := by sorry
