-- Prove2me | Theorems.Thm_XORFullTilt_Hardness_cube_soundness
-- name    : XORFullTilt.Hardness.cube_soundness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:52:32.173343+00:00
-- url     : https://prove2.me/theorems/2fdbcd23-cc9a-4f11-b076-ab05cb339baf
-- title:
--   Lemma 4.6 — soundness rounding, C=301814
-- statement:
--   There is a state-construction map $\Phi$ taking each unit state $\psi\in H_A\otimes H_B$ to a unit state $\Phi(\psi)\in H_A\otimes H_A$, chosen independently of the measurements and of $\varepsilon$. For every $\varepsilon$-optimal PVM strategy for the tilted cube with this state $\psi$, there is an eight-outcome POVM $\Pi$ on $H_A$ such that
--   $$\frac13\sum_{a:\,a_1\oplus a_2\oplus a_3=0}\langle\Phi(\psi)|\Pi_a\otimes(P^{011}_{a_1}+P^{101}_{a_2}+P^{110}_{a_3})|\Phi(\psi)\rangle\ge1-301814\varepsilon.$$
--   The map is fixed before quantifying over all local PVMs; the POVM may depend on them. Odd-parity POVM outcomes are permitted, but only even outcomes contribute to the score. This preserves the source's state-uniformity clause.
--
--   Differences from the source:
--   - encoding: even questions 000,011,101,110 and odd questions 111,100,010,001 → each ordered question set is Fin 4; reason: matching indices are complements, so all 16 signs and all response functions are preserved
--   - encoding: finite-dimensional complex Hilbert spaces → complex coordinate matrices on Fin d and Fin e; reason: orthonormal coordinates represent every finite-dimensional instance, without a dimension bound
--   - encoding: nonnegative approximation error ε → ε is an NNReal, coerced to a real in formulas; reason: this makes the nonnegative-error convention explicit without excluding an admissible error
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p.25, Lemma 4.6

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_TiltedGame

open Matrix Kronecker

namespace XORFullTilt.Hardness

/-- Lemma 4.6, p.25. The map is selected before every measurement and every error. -/
theorem cube_soundness :
    ∃ Φ : ∀ d e : ℕ, State d e → State d d,
      ∀ (d e : ℕ) (ψ : State d e) (P : Fin 4 → Measurement Bool d)
        (Q : Fin 4 → Measurement Bool e),
        (∀ x, IsPVM (P x)) → (∀ y, IsPVM (Q y)) → ∀ ε : NNReal,
        strategyValue tiltedCube.game {state := ψ, alice := P, bob := Q} ≥
          quantumValue tiltedCube.game - (ε : ℝ) →
        ∃ Pi : Measurement Triple d,
          relationScore (Φ d e ψ) Pi (fun u => P u.succ) ≥ 1-301814*(ε : ℝ) := by sorry

end XORFullTilt.Hardness
