-- Prove2me | Theorems.Thm_section5_sampled_gaussian_toLp_ne_zero
-- name    : section5_sampled_gaussian_toLp_ne_zero
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:56:42.192763+00:00
-- url     : https://prove2.me/theorems/a394d064-3f23-4f90-9d56-d592ae45577f
-- title:
--   The sampled Gaussian amplitude is nonzero in L²
-- statement:
--   Let n,M be natural with M>0. On R^n let G_(n,M) be the standard Gaussian square-root density evaluated at the source's rounded centered grid points and restricted to its grid box. Its Lebesgue L² class is nonzero: $$[G_{n,M}]_{L^2}\ne0.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5PhaseStateError.lean, lines 27–28.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example Aux_w_53_hermite

theorem section5_sampled_gaussian_toLp_ne_zero (n M : ℕ) (hM : 0 < M) :
    (section5_sampled_gaussian_memLp n M hM).toLp (section5_sampled_gaussian_amplitude n M) ≠ 0 := by sorry
