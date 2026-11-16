-- Prove2me | Theorems.Thm_XORFullTilt_Hardness_Supplement_classical_reduction
-- name    : XORFullTilt.Hardness.Supplement.classical_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:26:07.349195+00:00
-- url     : https://prove2.me/theorems/dfa2814c-5724-4a3d-8925-363e560f5284
-- title:
--   Theorem 2.13 — classical gadget bounds (corrected: completeness intercept 3/4)
-- statement:
--   Let $S$ be any E3-LIN system, $\pi$ any real probability law on its equations, $G=G(S,\pi)$ its classical game, and $\widetilde G$ the XOR relaxation of the exact published cube reduction. For every real $\varepsilon\ge0$, both implications hold:
--   $$\omega(G)\ge1-\varepsilon\ \Longrightarrow\ \omega(\widetilde G)\ge\frac34-\frac{3\varepsilon}{8},$$
--   $$\omega(G)<\frac56+\varepsilon\ \Longrightarrow\ \omega(\widetilde G)<\frac{11}{16}+\frac{3\varepsilon}{8}.$$
--   These are the classical completeness and strict soundness estimates of the gadget. Zero equation weights are permitted. The completeness intercept corrects the source's printed arithmetic error.
--
--   Differences from the source:
--   - correction: completeness conclusion has intercept 1 → completeness conclusion has intercept 3/4; reason: a single parity-zero equation has input classical value 1 and output cube value 3/4; at epsilon=1/100 the printed bound demands 3/4 >= 797/800, which is false; the page's own weighted-average calculation has intercept 3/4
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p. 15, Theorem 2.13

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_E3LIN

open Matrix Kronecker

namespace XORFullTilt.Hardness.Supplement

/-- Theorem 2.13, p.15 (corrected: completeness intercept 3/4).
    A single parity-zero equation gives input value 1 and cube value 3/4,
    contradicting the printed intercept 1 even at ε=1/100. -/
theorem classical_reduction {m : ℕ} (S : E3System m) (π : PMF (E3Question S))
    (ε : ℝ) (hε : 0 ≤ ε) :
    (classicalValue (e3Game S π) ≥ 1 - ε →
      classicalValue (xorRelaxation (cubeReduction S π)).game ≥ (3/4 : ℝ) - 3*ε/8) ∧
    (classicalValue (e3Game S π) < (5/6 : ℝ) + ε →
      classicalValue (xorRelaxation (cubeReduction S π)).game < (11/16 : ℝ) + 3*ε/8) := by sorry
end XORFullTilt.Hardness.Supplement
