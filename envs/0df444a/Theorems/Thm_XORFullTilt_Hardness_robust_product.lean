-- Prove2me | Theorems.Thm_XORFullTilt_Hardness_robust_product
-- name    : XORFullTilt.Hardness.robust_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:52:34.418795+00:00
-- url     : https://prove2.me/theorems/6380c011-b343-4e31-a6d5-a5c660004227
-- title:
--   Proposition 4.5 — robust product relation
-- statement:
--   Consider an $\varepsilon$-optimal quantum strategy for the tilted cube, with unitary binary observables (no condition is imposed on $A_{000}$, which affects neither the value nor the conclusion). For every permutation $\sigma$ of $011,101,110$,
--   $$\left\|\bigl((A_{\sigma(011)}A_{\sigma(101)}A_{\sigma(110)}-I)\otimes I\bigr)\psi\right\|\le68\sqrt{13\varepsilon}.$$
--   The same input state is used for every observable order. This includes the displayed source order and the following observable-order clause.
--
--   Differences from the source:
--   - encoding: even questions 000,011,101,110 and odd questions 111,100,010,001 → each ordered question set is Fin 4; reason: matching indices are complements, so all 16 signs and all response functions are preserved
--   - encoding: finite-dimensional complex Hilbert spaces → complex coordinate matrices on Fin d and Fin e; reason: orthonormal coordinates represent every finite-dimensional instance, without a dimension bound
--   - encoding: nonnegative approximation error ε → ε is an NNReal, coerced to a real in formulas; reason: this makes the nonnegative-error convention explicit without excluding an admissible error
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p.23, Proposition 4.5

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_TiltedGame

open Matrix Kronecker

namespace XORFullTilt.Hardness

/-- Proposition 4.5, p.23, including every order of the three observables.
    No convention is imposed at 000: neither the value nor the conclusion depends on it. -/
theorem robust_product {d e : ℕ} (S : QuantumStrategy (Fin 4) (Fin 4) Bool Bool d e)
    (ε : NNReal)
    (hnear : strategyValue tiltedCube.game S ≥ quantumValue tiltedCube.game - (ε : ℝ))
    (hA : ∀ x, star (observable (S.alice x)) * observable (S.alice x) = 1)
    (hB : ∀ y, star (observable (S.bob y)) * observable (S.bob y) = 1) :
    ∀ σ : Equiv.Perm (Fin 3),
      vectorNorm (((((observable (S.alice (σ 0).succ)) *
        (observable (S.alice (σ 1).succ)) *
        (observable (S.alice (σ 2).succ))) - 1) ⊗ₖ (1 : Matrix (Fin e) (Fin e) ℂ)) *ᵥ S.state.vec) ≤
        68 * Real.sqrt (13*(ε : ℝ)) := by sorry

end XORFullTilt.Hardness
