-- Prove2me | Theorems.Thm_section5_wave_sum_product_integral
-- name    : section5_wave_sum_product_integral
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:06:42.527384+00:00
-- url     : https://prove2.me/theorems/fef85d08-6a51-4dfb-b731-320b285d7e57
-- title:
--   Inner product of two finite Hermite wave sums
-- statement:
--   Write $\phi(x)=(2\pi)^{-1/2}e^{-x^2/2}$ and $\psi_k(x)=\sqrt{\phi(x)}H_k(x)/\sqrt{k!}$, where $H_k$ is the probabilists' Hermite polynomial. Let $I,J$ be finite index types, $a_i,b_j\in\mathbb R$, and $u_i,v_j\in\mathbb N$. Then
--
--   $$
--   \int_{\mathbb R}\left(\sum_{i\in I}a_i\psi_{u_i}(x)\right)\left(\sum_{j\in J}b_j\psi_{v_j}(x)\right)\,dx=\sum_{i\in I}\sum_{j\in J}a_i b_j\mathbf1_{u_i=v_j}.
--   $$
--
--   Repeated degree indices are allowed; the identity evaluates finite Hermite expansion inner products.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; not asserted to be a separately numbered result of the paper. Exact local source: Solutions/Section5HermiteWavefunctions.lean, section5_wave_sum_product_integral, lines 85–108.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Mathlib
import Theorems.Thm_Aux_w_53_hermite_h1D_orthonormal_aux
set_option autoImplicit false
open MeasureTheory Aux_w_53_hermite

theorem section5_wave_sum_product_integral {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : κ → ℝ) (u : ι → ℕ) (v : κ → ℕ) :
    (∫ x : ℝ, (∑ i, a i*section5_hermite_wave (u i) x)*
      (∑ j, b j*section5_hermite_wave (v j) x)) =
      ∑ i, ∑ j, (a i*b j)*(if u i=v j then 1 else 0) := by sorry
