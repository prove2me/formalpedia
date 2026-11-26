-- Prove2me | Theorems.Thm_section5_clean_qht_coefficient_transfer
-- name    : section5_clean_qht_coefficient_transfer
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:04:33.598724+00:00
-- url     : https://prove2.me/theorems/c393f86c-9dc0-4505-807e-d0b5dfbb0eb3
-- title:
--   Conditional coefficient transfer through a clean subspace
-- statement:
--   Let $e:\alpha\hookrightarrow\beta$ embed finite basis sets, let $E:\mathbb C^\alpha\to\mathbb C^\beta$ be its zero-padding isometry, let $U$ be a unitary on $\mathbb C^\beta$, and let $S:\mathbb C^\alpha\to\mathbb C^\beta$ be linear. Suppose $n\ge1$, $0<\eta<1/2$, and $\|UEv-Sv\|\le\eta/(4n)$ for every unit vector $v$. For $\|\psi\|\le1$ and any coefficient vector $c$,
--
--   $$\|(S^{\otimes n})^*\psi-c\|\le\eta/2\quad\Longrightarrow\quad\|((UE)^{\otimes n})^*\psi-c\|\le\eta.$$
--
--   This is a conditional clean-subspace estimate for a supplied unitary and synthesis approximation. It supplies the coefficient-transfer step used in a quantum Hermite transform analysis.
-- source:
--   Original auxiliary clean-subspace transfer result supporting Section 5.1 of Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3. Formalization: Solutions/Section5CleanSubspace.lean, lines 60–83.

import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_Section5Verified_Section5CleanSubspace
import Definitions.Def_Section5Verified_Section5HermiteTransfer
import Mathlib
import Theorems.Thm_section5_tensor_inverse_coefficient_transfer
set_option autoImplicit false
set_option maxHeartbeats 1000000
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem section5_clean_qht_coefficient_transfer
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) (U : EuclideanSpace ℂ β ≃ₗᵢ[ℂ] EuclideanSpace ℂ β)
    (S : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)
    (n : ℕ) (hn : 1 ≤ n) (η : ℝ) (hη : 0 < η) (hη' : η < 1/2)
    (hsynth : ∀ c : EuclideanSpace ℂ α, ‖c‖ = 1 →
      ‖U (section5_basis_embedding e c)-S c‖ ≤ η/(4*n))
    (ψ : EuclideanSpace ℂ (Fin n → β)) (hψ : ‖ψ‖ ≤ 1)
    (c : EuclideanSpace ℂ (Fin n → α))
    (hdisc : ‖ContinuousLinearMap.adjoint (section5_tensor_power S n) ψ-c‖ ≤ η/2) :
    ‖ContinuousLinearMap.adjoint
        (section5_tensor_power
          (U.toLinearIsometry.toContinuousLinearMap ∘L
            (section5_basis_embedding e).toContinuousLinearMap) n) ψ-c‖ ≤ η := by sorry
