-- Prove2me | Theorems.Thm_XORFullTilt_Hardness_relaxation_comparison
-- name    : XORFullTilt.Hardness.relaxation_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:52:36.180566+00:00
-- url     : https://prove2.me/theorems/c9c81766-0dca-4248-a177-65a2dc7952ee
-- title:
--   Lemma 3.3 — XOR relaxation comparison
-- statement:
--   For every tilted XOR game $G$, let $G_{\rm XOR}$ denote its XOR relaxation. Then
--   $$\omega(G_{\rm XOR})=\omega(G),\qquad \omega^*(G_{\rm XOR})\ge\omega^*(G).$$
--   Both values are taken over their full classical or finite-dimensional quantum strategy classes. The result compares the tilt with its relaxation without imposing full support or special shared states.
--
--   Differences from the source: none.
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p.17, Lemma 3.3

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_TiltedGame

open Matrix Kronecker

namespace XORFullTilt.Hardness

/-- Lemma 3.3, p.17; both classical equality and quantum comparison. -/
theorem relaxation_comparison {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (G : TiltedGame X Y) :
    classicalValue (xorRelaxation G).game = classicalValue G.game ∧
    quantumValue (xorRelaxation G).game ≥ quantumValue G.game := by sorry

end XORFullTilt.Hardness
