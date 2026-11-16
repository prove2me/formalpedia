-- Prove2me | Theorems.Thm_XORFullTilt_Hardness_Supplement_optimal_support
-- name    : XORFullTilt.Hardness.Supplement.optimal_support
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:26:48.097464+00:00
-- url     : https://prove2.me/theorems/4010bb9b-004e-4f94-b70e-7803aa9407f5
-- title:
--   Lemma 3.7 — optimal cube observables on the reduced support
-- statement:
--   Let $\psi\in\mathbb C^d\otimes\mathbb C^e$ and binary measurement families give an optimal strategy for the tilted cube, and suppose all associated observables are unitary. Let $K_A$ be the support of Alice's reduced density operator. Then $A_{011},A_{101},A_{110}$ each preserve $K_A$, their restrictions commute pairwise, and
--   $$A_{011}A_{101}A_{110}v=v\qquad(v\in K_A).$$
--   The statement includes support preservation as well as both restricted operator identities. It does not assert a global identity outside the support.
--
--   Differences from the source:
--   - encoding: finite complex Hilbert spaces and vertex labels 011,101,110 → coordinate spaces Fin d and labels 1,2,3; support is range of the reduced density matrix; reason: orthonormal coordinates and the published cube ordering preserve every strategy and the actual reduced support
--   - generalization: the correlation convention sets the ignored observable A000 to I → the strategy may have any unitary observable at question 000; reason: replacing this unused measurement by the deterministic zero measurement preserves the score, state, reduced support and all three asserted conclusions; choosing A000=I recovers every source instance
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p. 19, Lemma 3.7

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_TiltedGame
import Definitions.Def_XORFullTilt_Hardness_Supplement_ReducedSupport

open Matrix Kronecker

namespace XORFullTilt.Hardness.Supplement

/-- Lemma 3.7: all three clauses hold on Alice's actual reduced support. -/
theorem optimal_support {d e : ℕ} (S : QuantumStrategy (Fin 4) (Fin 4) Bool Bool d e)
    (hoptimal : strategyValue tiltedCube.game S = quantumValue tiltedCube.game)
    (hA : ∀ x, star (observable (S.alice x)) * observable (S.alice x) = 1)
    (hB : ∀ y, star (observable (S.bob y)) * observable (S.bob y) = 1) :
    (∀ i : Fin 3, ∀ v ∈ aliceSupport S.state,
      observable (S.alice i.succ) *ᵥ v ∈ aliceSupport S.state) ∧
    (∀ i j : Fin 3, ∀ v ∈ aliceSupport S.state,
      (observable (S.alice i.succ) * observable (S.alice j.succ)) *ᵥ v =
        (observable (S.alice j.succ) * observable (S.alice i.succ)) *ᵥ v) ∧
    (∀ v ∈ aliceSupport S.state,
      (observable (S.alice 1) * observable (S.alice 2) * observable (S.alice 3)) *ᵥ v = v) := by sorry
end XORFullTilt.Hardness.Supplement
