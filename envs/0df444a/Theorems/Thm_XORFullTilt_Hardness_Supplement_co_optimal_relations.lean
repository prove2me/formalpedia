-- Prove2me | Theorems.Thm_XORFullTilt_Hardness_Supplement_co_optimal_relations
-- name    : XORFullTilt.Hardness.Supplement.co_optimal_relations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:29:13.406574+00:00
-- url     : https://prove2.me/theorems/4fe0ad99-2440-4322-83d0-f3e97f09121f
-- title:
--   Lemma 6.3 — state-dependent commuting cube relations
-- statement:
--   Let a commuting-operator strategy on any complete complex Hilbert space have a unit state $\psi$ and attain the commuting value of the tilted cube. Suppose all its binary observables are unitary. Then
--   $$[A_x,A_y]\psi=0\qquad(x,y\in\{011,101,110\}),\qquad A_{011}A_{101}A_{110}\psi=\psi.$$
--   These are equalities on the state vector. No global same-party commutation identity and no finite-dimensionality hypothesis are imposed.
--
--   Differences from the source:
--   - encoding: possibly infinite-dimensional complex Hilbert spaces, POVMs and state correlations → complete complex inner-product spaces, bounded self-adjoint positive effects and a norm-one vector; probabilities are real parts of Born expectations; reason: these are the same Hilbert-space models; positivity is a nonnegative quadratic form and no dimension bound or trace condition is added
--   - generalization: the correlation convention sets the ignored observable A000 to I → the strategy may have any unitary observable at question 000; reason: replacing this unused measurement by the deterministic zero measurement preserves the score, state and both asserted state-vector identities; choosing A000=I recovers every source instance
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p. 31, Lemma 6.3

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_Supplement_CommutingModel

open Matrix Kronecker

namespace XORFullTilt.Hardness.Supplement

/-- Lemma 6.3, with state-vector identities rather than global identities. -/
theorem co_optimal_relations (S : COStrategy (Fin 4) (Fin 4) Bool Bool)
    (hoptimal : coStrategyValue tiltedCube.game S = coValue tiltedCube.game)
    (hA : ∀ x, star (coAliceObservable S x) * coAliceObservable S x = 1)
    (hB : ∀ y, star (coBobObservable S y) * coBobObservable S y = 1) :
    (∀ i j : Fin 3,
      (coAliceObservable S i.succ * coAliceObservable S j.succ -
        coAliceObservable S j.succ * coAliceObservable S i.succ) S.Ω = 0) ∧
    (coAliceObservable S 1 * coAliceObservable S 2 *
      coAliceObservable S 3) S.Ω = S.Ω := by sorry
end XORFullTilt.Hardness.Supplement
