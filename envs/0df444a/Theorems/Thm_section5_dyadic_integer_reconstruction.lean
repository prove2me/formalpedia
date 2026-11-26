-- Prove2me | Theorems.Thm_section5_dyadic_integer_reconstruction
-- name    : section5_dyadic_integer_reconstruction
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:17:09.284254+00:00
-- url     : https://prove2.me/theorems/0cbf594d-d45b-473e-bb8b-77b90d7d8130
-- title:
--   Conditional direction recovery from an integer matrix power
-- statement:
--   Let n≥1, A a complex integer matrix, L=2^(−q)op(A) self-adjoint, 0<ε<1, 2^(k+1)≥800n/ε and 2^f≥144n²4^(k+1)/ε. Let j maximize the column score of A^(k+1), let c_j be its larger real or imaginary column, and put r=2^(−(q+1)(k+1))c_j. If real unit w satisfies ‖L−ww*‖≤ε/2000, then $$Q_f(r)\ne0,\qquad\min_{s\in\{\pm1\}}\|Q_f(r)/\|Q_f(r)\|-sw\|\le\varepsilon/6.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5IntegerSpectralBridge.lean, lines 197–211.

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
import Definitions.Def_Section5Verified_Section5FixedPointQuantization
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Definitions.Def_Section5Verified_Section5QuantizedReconstruction
import Mathlib
import Theorems.Thm_section5_dyadic_max_score_column
import Theorems.Thm_section5_integer_scaled_candidate
import Theorems.Thm_section5_power_column_estimator
import Theorems.Thm_section5_power_column_magnitude_bounds
import Theorems.Thm_section5_uniform_power_output_quantization
import Theorems.Thm_section5_unnormalized_real_recovery
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_dyadic_integer_reconstruction {n : ℕ} (hn : 1 ≤ n)
    (A : Section5IntegerMatrix n) (q k f : ℕ)
    (hA : IsSelfAdjoint (A.dyadicOperator q))
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hiter : 800*(n:ℝ)/ε ≤ (2:ℝ)^(k+1))
    (hbits : 144*(n:ℝ)^2*(4:ℝ)^(k+1)/ε ≤ (2:ℝ)^f)
    (j : Fin n)
    (hmax : ∀ i, (A.power (k+1)).columnScore i ≤ (A.power (k+1)).columnScore j)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1)
    (herror : ‖A.dyadicOperator q-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/2000) :
    let r := ((2:ℝ)^((q+1)*(k+1)))⁻¹ •
      (WithLp.toLp 2 (fun i => ((A.power (k+1)).realCandidateAt j i:ℝ)))
    section5_quantize_vector f r ≠ 0 ∧
      (‖NormedSpace.normalize (section5_quantize_vector f r)-w‖ ≤ ε/6 ∨
        ‖NormedSpace.normalize (section5_quantize_vector f r)+w‖ ≤ ε/6) := by sorry
