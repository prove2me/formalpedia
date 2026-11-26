-- Prove2me | Theorems.Thm_section5_projDist_inverse_coefficients
-- name    : section5_projDist_inverse_coefficients
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:08:19.889054+00:00
-- url     : https://prove2.me/theorems/f221c2b1-effc-4619-b904-b7758c502861
-- title:
--   Projected inverse-state distance as a coefficient norm
-- statement:
--   Let $n,q,a,D$ be natural numbers with $D\le2^q$, and let $w\in\mathbb R^n$. Let $E$ embed the degree array $\alpha\in\{0,\ldots,D-1\}^n$ as $n$ most-significant-bit-first $q$-qubit registers followed by $a$ zero ancillas. Write $h_w$ for the vector of Gaussian Hermite coefficients of the homogeneous threshold function with normal $w$. For any linear operator $U$ on the full register and any vector $\psi$,
--
--   $$\operatorname{projDist}_{n,q,a,D}(w,U^*\psi)=\|(UE)^*\psi-h_w\|_2.$$
--
--   This identifies the projected distance used in the Section 5 interface with an ordinary finite coefficient error, including the clean-ancilla convention.
-- source:
--   Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1, projected Hermite coefficients and Eq. (159); exact auxiliary identity: Solutions/Section5CleanSubspace.lean, lines 119–128. Definition context: Definitions/Def_QuantumLTF_Membership_Supplement_projDist.lean.

import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_Section5Verified_Section5CleanSubspace
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem section5_projDist_inverse_coefficients (n q a D : ℕ) (hD : D ≤ 2^q)
    (w : EuclideanSpace ℝ (Fin n))
    (U : EuclideanSpace ℂ (Qubits (n*q+a)) →L[ℂ] EuclideanSpace ℂ (Qubits (n*q+a)))
    (ψ : EuclideanSpace ℂ (Qubits (n*q+a))) :
    projDist n q a D w (ContinuousLinearMap.adjoint U ψ) =
      ‖ContinuousLinearMap.adjoint
          (U ∘L (section5_basis_embedding (section5_clean_degree_encoding n q a D hD)).toContinuousLinearMap) ψ-
        section5_ideal_hermite_coefficients n D w‖ := by sorry
