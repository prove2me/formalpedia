-- Prove2me | Theorems.Thm_XORFullTilt_Hardness_quantum_cubes
-- name    : XORFullTilt.Hardness.quantum_cubes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:52:29.836112+00:00
-- url     : https://prove2.me/theorems/d2321978-2f59-44bb-95d2-2a589ed608fc
-- title:
--   Lemma 3.6 — quantum values of both cubes
-- statement:
--   The tilted cube and ordinary cube have quantum values
--   $$\omega^*(G_{\rm tilt})=\omega^*(G_{\square})=\frac34.$$
--   The supremum ranges over all finite complex dimensions and arbitrary POVMs. Both equalities are included; this is the common value used by the robust estimates.
--
--   Differences from the source:
--   - encoding: even questions 000,011,101,110 and odd questions 111,100,010,001 → each ordered question set is Fin 4; reason: matching indices are complements, so all 16 signs and all response functions are preserved
--   - encoding: finite-dimensional complex Hilbert spaces → complex coordinate matrices on Fin d and Fin e; reason: orthonormal coordinates represent every finite-dimensional instance, without a dimension bound
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p.18, Lemma 3.6

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_TiltedGame

open Matrix Kronecker

namespace XORFullTilt.Hardness

/-- Lemma 3.6, p.18. -/
theorem quantum_cubes :
    quantumValue tiltedCube.game = (3/4 : ℝ) ∧
    quantumValue cube.game = (3/4 : ℝ) := by sorry

end XORFullTilt.Hardness
