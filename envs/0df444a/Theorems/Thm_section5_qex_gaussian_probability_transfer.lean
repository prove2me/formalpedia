-- Prove2me | Theorems.Thm_section5_qex_gaussian_probability_transfer
-- name    : section5_qex_gaussian_probability_transfer
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:33:46.279955+00:00
-- url     : https://prove2.me/theorems/d6893e68-c7aa-4825-bdda-ab882a22709e
-- title:
--   Finite Gaussian grid probability transfer
-- statement:
--   Let n,q be natural numbers, q>0, M=2^q≥128n², and S a measurable subset of real n-dimensional Euclidean space. Let Z have normalized Gaussian grid weights on the centered M-point product grid, and let X be standard Gaussian with componentwise grid rounding R_M. Then $$|\Pr[Z\in S]-\Pr[R_MX\in S]|\le8n\sqrt{32/M}+4\sqrt{2n}e^{-\pi M/4}.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5FiniteProbabilityTransfer.lean, lines 132–138.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5FiniteCoefficientTransfer
import Definitions.Def_Section5Verified_Section5GaussianProbabilityTransfer
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5GridPhaseMatchesQEX
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Definitions.Def_Section5Verified_Section5PhysicalHermiteGrid
import Mathlib
import Theorems.Thm_section5_gaussian_event_probability_transfer
import Theorems.Thm_section5_grid_exp_sum
import Theorems.Thm_section5_grid_lift_norm
import Theorems.Thm_section5_l2_norm_sq
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership

open Classical in
theorem section5_qex_gaussian_probability_transfer (n q : ℕ) (hq : 0 < q)
    (hsize : 128*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : MeasurableSet S) :
    |(∑ z : Qubits (n*q), if gridPoint z ∈ S then
        gridWeight z/(∑ y : Qubits (n*q), gridWeight y) else 0)-
      (stdGaussian (EuclideanSpace ℝ (Fin n))).real {x | roundVec (2^q) x ∈ S}| ≤
        8*n*Real.sqrt (32/(2:ℝ)^q)+4*Real.sqrt (2*n)*Real.exp (-Real.pi*(2:ℝ)^q/4) := by sorry
