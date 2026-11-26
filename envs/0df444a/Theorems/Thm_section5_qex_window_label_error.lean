-- Prove2me | Theorems.Thm_section5_qex_window_label_error
-- name    : section5_qex_window_label_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:37:08.379179+00:00
-- url     : https://prove2.me/theorems/694cda78-2ff7-5baa-8564-c1dd47ab847b
-- title:
--   Window truncation error for Gaussian grid labels
-- statement:
--   Let n,q be natural numbers, q>0, M=2^q≥128n², u a real unit vector, and P,H positive integers. Put δ=√(4π/M), and let W be the centered real-window map of period parameter P and height H in the source. For normalized Gaussian grid Z, $$\Pr[\operatorname{sgn}\langle u,Z\rangle\ne\operatorname{sgn}\langle u,WZ\rangle]\le\sqrt{8n/M}+2ne^{-(\delta HP-\delta)^2/2}+\frac{2\delta(P+2)\sqrt n}{\sqrt{2\pi}}+8n\sqrt{32/M}+4\sqrt{2n}e^{-\pi M/4}.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5WindowQEXError.lean, lines 73–84.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5RealWindow
import Definitions.Def_Section5Verified_Section5SignedWindow
import Mathlib
import Theorems.Thm_section5_coordinate_approximation_norm
import Theorems.Thm_section5_gaussian_cube_tail
import Theorems.Thm_section5_gaussian_inner_strip
import Theorems.Thm_section5_qex_gaussian_probability_transfer
import Theorems.Thm_section5_real_window_error
import Theorems.Thm_section5_roundCoord_error
import Theorems.Thm_section5_rounding_label_probability
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership

open Classical in
theorem section5_qex_window_label_error {n q : ℕ} (hq : 0 < q)
    (hsize : 128*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖=1)
    (P H : ℤ) (hP : 0 < P) (hH : 0 < H) :
    (∑ z : Qubits (n*q),
      if ltf u 0 (gridPoint z) ≠
          ltf u 0 (section5_real_window_vec P H (gridSpacing (2^q)) (gridPoint z)) then
        gridWeight z/(∑ y : Qubits (n*q), gridWeight y) else 0) ≤
      Real.sqrt (8*n/(2:ℝ)^q)+
      2*n*Real.exp (-(gridSpacing (2^q)*H*P-gridSpacing (2^q))^2/2)+
      2*((gridSpacing (2^q)*(P+2))*Real.sqrt n)/Real.sqrt (2*Real.pi)+
      (8*n*Real.sqrt (32/(2:ℝ)^q)+4*Real.sqrt (2*n)*Real.exp (-Real.pi*(2:ℝ)^q/4)) := by sorry
