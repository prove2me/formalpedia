-- Prove2me | Theorems.Thm_section5_tensor_grid_vector_bits
-- name    : section5_tensor_grid_vector_bits
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:58:47.539836+00:00
-- url     : https://prove2.me/theorems/58b3dc4a-e1ff-4976-a716-657b4c98ff5d
-- title:
--   Grid samples coincide with the physical discrete Hermite tensor
-- statement:
--   Let $n,D\in\mathbb N$, $q\ge1$, and $a\in\{0,\ldots,D-1\}^n$. Put $M=2^q$, $\delta=\sqrt{4\pi/M}$, and $R=M\delta/2$. Let $\psi_a(x)=\prod_i\sqrt{\varphi(x_i)}H_{a_i}(x_i)/\sqrt{a_i!}$ be the tensor Hermite wavefunction. Sample it with cell-volume normalization, $v_a(j)=\delta^{n/2}\psi_a(-R+\delta j)$, and reindex each grid index by its most-significant-bit-first $q$-bit encoding. If $d_{q,k}$ denotes the public discrete Hermite ket, then
--
--   $$v_a(N(z_1),\ldots,N(z_n))=\prod_i d_{q,a_i}(z_i).$$
--
--   This exactly identifies the grid-vector normalization with the physical discrete Hermite tensor used on qubit registers.
-- source:
--   Original physical-grid identification for Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1. Formalization: Solutions/Section5PhysicalHermiteGrid.lean, lines 77–96; the discrete Hermite normalization is specified in Definitions/Def_QuantumLTF_Example_HermiteModel.lean.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Definitions.Def_Section5Verified_Section5MultivariateSampling
import Definitions.Def_Section5Verified_Section5PhysicalHermiteGrid
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example Aux_w_53_hermite

theorem section5_tensor_grid_vector_bits (n q D : ℕ) (hq : 0 < q) (a : Fin n → Fin D) :
    section5_grid_bit_isometry n q
      (section5_grid_vector n (2^q) (section5_tensor_family (section5_complex_wave D) n a)) =
      section5_discrete_hermite_tensor n q D a := by sorry
