-- Prove2me | Theorems.Thm_section5_lemma_5_1
-- name    : section5_lemma_5_1
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:45:46.67782+00:00
-- url     : https://prove2.me/theorems/cf5b1194-15bb-5dec-a2e8-01eed6d25398
-- title:
--   Lemma 5.1: discrete QEX Hermite coefficient approximation
-- statement:
--   Let $n,q,D\in\mathbb N$ with $q\ge1$, $D\ge1$, and $M=2^q\ge64n^2(D+1)$, and let $w\in\mathbb R^n$ be a unit vector. Let $f_w(x)=\operatorname{sgn}\langle w,x\rangle$, let $\widehat f_w(a)$ be its Gaussian Hermite coefficients, and let $\Psi_{w,q}(z)=f_w(x_z)\sqrt{p(z)}$ be the normalized phase input on the centered grid, with $p(z)$ proportional to $e^{-\|x_z\|^2/2}$. Write $d_a$ for the flattened tensor of public discrete Hermite kets of degrees $a_i<D$. Then
--
--   $$\left(\sum_{a\in\{0,\ldots,D-1\}^n}|\langle d_a,\Psi_{w,q}\rangle-\widehat f_w(a)|^2\right)^{1/2}\le24n\sqrt{\frac{D+1}M}+2(8n/M)^{1/4}+2\sqrt{2n}\,e^{-\pi M/4}.$$
--
--   This is the discretization estimate for the exact public QEX phase input and discrete Hermite normalization.
-- source:
--   Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5.1, Lemma 5.1. Formalization: Solutions/Section5DiscretizationLemma.lean, lines 36–46.

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
import Definitions.Def_Section5Verified_Section5DiscretizationLemma
import Definitions.Def_Section5Verified_Section5GridPhaseMatchesQEX
import Definitions.Def_Section5Verified_Section5PhysicalHermiteGrid
import Mathlib
import Theorems.Thm_section5_bit_coefficient_error_51
import Theorems.Thm_section5_bit_phase_state_eq_qex_phase
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem section5_lemma_5_1 (n q D : ℕ) (hq : 0 < q) (hD : 1 ≤ D)
    (hsize : 64*(n:ℝ)^2*(D+1) ≤ (2:ℝ)^q) (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) :
    Real.sqrt (∑ a : Fin n → Fin D,
      ‖inner ℂ (section5_flat_hermite_tensor n q D a) (section5_qex_phase_input w q)-
        (hermCoeff w (fun i => (a i : ℕ)) : ℂ)‖^2) ≤
      24*n*Real.sqrt ((D+1)/(2:ℝ)^q)+2*(8*n/(2:ℝ)^q)^(1/4:ℝ)+
        2*Real.sqrt (2*n)*Real.exp (-Real.pi*(2:ℝ)^q/4) := by sorry
