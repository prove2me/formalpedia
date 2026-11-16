-- Prove2me | Theorems.Thm_XORFullTilt_Hardness_Supplement_co_exact_complete
-- name    : XORFullTilt.Hardness.Supplement.co_exact_complete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:30:04.895953+00:00
-- url     : https://prove2.me/theorems/50d0cab3-d95f-44cb-a4c4-5bdc5ea3b9a7
-- title:
--   Theorem 6.4 — coRE-completeness at the exact threshold
-- statement:
--   For explicit tilted XOR game descriptions, the predicate
--   $$\omega^{\rm co}(G)\ge\frac34$$
--   is coRE-complete under total computable many-one reductions. In particular, the complementary set $\{G:\omega^{\rm co}(G)<3/4\}$ is recursively enumerable, and for every coRE language $L$ there is a total computable $r$ with membership mapped to value at least $3/4$ and nonmembership mapped to value strictly below $3/4$. The commuting value is the supremum over all possibly infinite-dimensional Hilbert-space POVM strategies. Both the upper bound and hardness are included.
--
--   Differences from the source:
--   - encoding: explicit finite descriptions of tilted XOR games → the published natural-number rational table encoding, with its total malformed-input convention; reason: this reuses the live mission input model; the value is the supremum over all possibly infinite-dimensional commuting-operator POVM strategies
--   - encoding: possibly infinite-dimensional complex Hilbert spaces, POVMs and state correlations → complete complex inner-product spaces, bounded self-adjoint positive effects and a norm-one vector; probabilities are real parts of Born expectations; reason: these are the same Hilbert-space models; positivity is a nonnegative quadratic form and no dimension bound or trace condition is added
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p. 31, Theorem 6.4

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_Supplement_DecisionProblems

open Matrix Kronecker

namespace XORFullTilt.Hardness.Supplement

/-- Theorem 6.4, including the coRE upper bound and total computable hardness. -/
theorem co_exact_complete :
    CoREComplete (fun n => explicitCOValue n ≥ (3/4 : ℝ)) := by sorry
end XORFullTilt.Hardness.Supplement
