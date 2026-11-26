-- Prove2me | Theorems.Thm_section5_wave_sum_integrable_product
-- name    : section5_wave_sum_integrable_product
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:01:36.569507+00:00
-- url     : https://prove2.me/theorems/c713f1af-e3b1-4d68-8c6d-5a8ceac2d4a0
-- title:
--   Integrability of products of finite Hermite wavefunction sums
-- statement:
--   Let I,J be finite index sets, a∈R^I, b∈R^J, and u:I→N, v:J→N. For ψ_k(x)=√φ(x)He_k(x)/√(k!), where φ is the standard Gaussian density, the real function F(x)=(Σ_i a_iψ_(u_i)(x))(Σ_j b_jψ_(v_j)(x)) is Lebesgue integrable: $$\int_{\mathbb R}|F(x)|\,dx<\infty.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5HermiteWavefunctions.lean, lines 65–68.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Aux_w_53_hermite

theorem section5_wave_sum_integrable_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : κ → ℝ) (u : ι → ℕ) (v : κ → ℕ) :
    Integrable (fun x => (∑ i, a i*section5_hermite_wave (u i) x)*
      (∑ j, b j*section5_hermite_wave (v j) x)) := by sorry
