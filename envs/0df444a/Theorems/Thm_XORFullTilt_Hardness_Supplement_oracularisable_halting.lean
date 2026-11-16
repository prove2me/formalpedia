-- Prove2me | Theorems.Thm_XORFullTilt_Hardness_Supplement_oracularisable_halting
-- name    : XORFullTilt.Hardness.Supplement.oracularisable_halting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:30:58.874202+00:00
-- url     : https://prove2.me/theorems/eb5719ac-013e-4d9c-8174-cd946eb2f8a3
-- title:
--   Theorem 6.10 — polynomial-time halting reduction for oracularisable strategies
-- statement:
--   For every real $0<\varepsilon<10^{-8}$, there exist a fixed polynomial-time succinct tilted-XOR verifier $V$ and a polynomial-time input map $R$ such that, for every binary program/input description $x$,
--   $$x\in\mathrm{HALT}\Longrightarrow\omega^*_{\rm orac}(G_{V,R(x)})\ge\frac34-\varepsilon,$$
--   $$x\notin\mathrm{HALT}\Longrightarrow\omega^*_{\rm orac}(G_{V,R(x)})<\frac34-10^{-8}.$$
--   The value uses arbitrary positive finite dimensions and normalized-trace PVM strategies whose cross-party effects commute only on positive-law question pairs. The verifier and map may depend on the fixed accuracy, but their polynomial bounds hold uniformly over all inputs. This evaluates the original game, without replacing it by an oracularised game.
--
--   Differences from the source:
--   - encoding: polynomial-time reduction from halting to succinct polynomial-time verifiers → binary universal partial-recursive program/input codes, a charged PolyTimeFun input map and a fixed published SuccinctVerifier; reason: the finite program syntax and explicit polynomial clocks certify actual runtime and polynomial tape/question lengths, while the original finite game is evaluated in the specified alternate strategy model
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p. 37, Theorem 6.10 and explicit-constant paragraph

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_Supplement_DecisionProblems

open Matrix Kronecker

namespace XORFullTilt.Hardness.Supplement

/-- Theorem 6.10, with its explicit thresholds and every positive gap parameter. -/
theorem oracularisable_halting (ε : ℝ) (hε : 0 < ε) (hsmall : ε < (1/100000000 : ℝ)) :
    ∃ R : MIPRE.Cost.PolyTimeFun (List Bool) (List Bool), ∃ V : SuccinctVerifier,
      (∀ x, haltingLanguage x → succinctOracularisableValue V (R x) ≥ (3/4 : ℝ) - ε) ∧
      (∀ x, ¬ haltingLanguage x →
        succinctOracularisableValue V (R x) < (3/4 : ℝ) - (1/100000000 : ℝ)) := by sorry
end XORFullTilt.Hardness.Supplement
