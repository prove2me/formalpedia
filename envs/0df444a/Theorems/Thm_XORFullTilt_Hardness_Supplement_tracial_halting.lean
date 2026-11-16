-- Prove2me | Theorems.Thm_XORFullTilt_Hardness_Supplement_tracial_halting
-- name    : XORFullTilt.Hardness.Supplement.tracial_halting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:31:41.854661+00:00
-- url     : https://prove2.me/theorems/4cfe862a-b03e-4e02-beb4-e812757f7ca2
-- title:
--   Theorem 6.14 — polynomial-time halting reduction for tracial strategies
-- statement:
--   For every real $0<\varepsilon<10^{-8}$, there exist a fixed polynomial-time succinct tilted-XOR verifier $V$ and a polynomial-time input map $R$ such that, for every binary program/input description $x$,
--   $$x\in\mathrm{HALT}\Longrightarrow\omega^*_{\rm tr}(G_{V,R(x)})\ge\frac34-\varepsilon,$$
--   $$x\notin\mathrm{HALT}\Longrightarrow\omega^*_{\rm tr}(G_{V,R(x)})<\frac34-10^{-8}.$$
--   The value is the supremum over all positive finite dimensions and two PVM families on the common complex space, with probabilities given by normalized traces of their products. No cross-party commutation condition is imposed. These explicit thresholds use the source's stated completeness consequence of Theorem 6.10, together with unrestricted quantum soundness, rather than an unspecified asymptotic rounding constant.
--
--   Differences from the source:
--   - encoding: polynomial-time reduction from halting to succinct polynomial-time verifiers → binary universal partial-recursive program/input codes, a charged PolyTimeFun input map and a fixed published SuccinctVerifier; reason: the finite program syntax and explicit polynomial clocks certify actual runtime and polynomial tape/question lengths, while the original finite game is evaluated in the specified alternate strategy model
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p. 39, Theorem 6.14 and explicit-constant paragraph

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_Supplement_DecisionProblems

open Matrix Kronecker

namespace XORFullTilt.Hardness.Supplement

/-- Theorem 6.14, with its explicit thresholds and every positive gap parameter. -/
theorem tracial_halting (ε : ℝ) (hε : 0 < ε) (hsmall : ε < (1/100000000 : ℝ)) :
    ∃ R : MIPRE.Cost.PolyTimeFun (List Bool) (List Bool), ∃ V : SuccinctVerifier,
      (∀ x, haltingLanguage x → succinctTracialValue V (R x) ≥ (3/4 : ℝ) - ε) ∧
      (∀ x, ¬ haltingLanguage x →
        succinctTracialValue V (R x) < (3/4 : ℝ) - (1/100000000 : ℝ)) := by sorry
end XORFullTilt.Hardness.Supplement
