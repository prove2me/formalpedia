-- Prove2me | Theorems.Thm_XORFullTilt_Hardness_cube_completeness
-- name    : XORFullTilt.Hardness.cube_completeness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:52:55.288429+00:00
-- url     : https://prove2.me/theorems/1350d0a8-b213-4da9-91f1-63c8da888c2c
-- title:
--   Lemma 4.7 — completeness with loss 3ε/8
-- statement:
--   Let $\psi\in H_A\otimes H_B$ be a unit shared state, let $P^{011},P^{101},P^{110}$ be binary PVMs on $H_B$, and let $\Pi$ be an eight-outcome PVM on $H_A$. Suppose
--   $$\frac13\sum_{a:\,a_1\oplus a_2\oplus a_3=0}\langle\psi|\Pi_a\otimes(P^{011}_{a_1}+P^{101}_{a_2}+P^{110}_{a_3})|\psi\rangle\ge1-\varepsilon.$$
--   There exist four binary PVMs $Q^y$ on $H_A$, one for each odd vertex, such that the tilted-cube strategy on $H_B\otimes H_A$ with state $\operatorname{swap}(\psi)$, Alice's original three measurements, $P^{000}_0=I$, $P^{000}_1=0$, and Bob's $Q^y$ is $\tfrac{3}{8}\varepsilon$-optimal:
--   $$\omega(G_{\rm tilt},p)\ge\omega^*(G_{\rm tilt})-\frac{3\varepsilon}{8}.$$
--   By Lemma 3.6 this is the bound $\omega(G_{\rm tilt},p)\ge\frac34-\frac{3\varepsilon}{8}$. No dimension enlargement or replacement of the given state or variable measurements occurs.
--
--   Differences from the source:
--   - encoding: even questions 000,011,101,110 and odd questions 111,100,010,001 → each ordered question set is Fin 4; reason: matching indices are complements, so all 16 signs and all response functions are preserved
--   - encoding: finite-dimensional complex Hilbert spaces → complex coordinate matrices on Fin d and Fin e; reason: orthonormal coordinates represent every finite-dimensional instance, without a dimension bound
--   - encoding: nonnegative approximation error ε → ε is an NNReal, coerced to a real in formulas; reason: this makes the nonnegative-error convention explicit without excluding an admissible error
--   - reading: the source places P on the second factor but writes its cube strategy with reversed party labels → the cube strategy uses the canonical swapped state, P on the first factor, and Q on the second; reason: the Born scalar is unchanged; all three original measurements and the shared state are preserved, with the zero-answer measurement at 000
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p.27, Lemma 4.7; p.28, its proof

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_TiltedGame

open Matrix Kronecker

namespace XORFullTilt.Hardness

/-- Lemma 4.7, p.27. The tensor swap resolves the source's reversed party labels;
    the input state and all three variable measurements are retained;
    the conclusion is `3ε/8`-optimality against the actual quantum value. -/
theorem cube_completeness {d e : ℕ} (ψ : State d e)
    (P : Fin 3 → Measurement Bool e) (Pi : Measurement Triple d)
    (hP : ∀ u, IsPVM (P u)) (hPi : IsPVM Pi) (ε : NNReal)
    (hnear : relationScore ψ Pi P ≥ 1-(ε : ℝ)) :
    ∃ Q : Fin 4 → Measurement Bool d, (∀ y, IsPVM (Q y)) ∧
      strategyValue tiltedCube.game
        { state := ψ.swap, alice := extendMeasurements P, bob := Q } ≥
          quantumValue tiltedCube.game - 3*(ε : ℝ)/8 := by sorry

end XORFullTilt.Hardness
