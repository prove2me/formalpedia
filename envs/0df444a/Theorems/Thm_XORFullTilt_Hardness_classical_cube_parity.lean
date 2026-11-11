-- Prove2me | Theorems.Thm_XORFullTilt_Hardness_classical_cube_parity
-- name    : XORFullTilt.Hardness.classical_cube_parity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:52:24.690542+00:00
-- url     : https://prove2.me/theorems/b4383357-a365-4e14-a312-7d01c402dfb5
-- title:
--   Lemma 2.12 — classical cube parity gap
-- statement:
--   Let $G_{\square}$ be the cube game. Its classical value is
--   $$\omega(G_{\square})=\frac34.$$
--   Among deterministic response functions $g,h$, success probability $3/4$ is attainable with $g(000)\oplus g(011)\oplus g(101)\oplus g(110)=0$. In the odd-parity class every deterministic strategy has value at most $5/8$, and that value is attained. Thus the latter class has exact maximum $5/8$.
--
--   This records both parity classes and their attainability.
--
--   Differences from the source:
--   - encoding: even questions 000,011,101,110 and odd questions 111,100,010,001 → each ordered question set is Fin 4; reason: matching indices are complements, so all 16 signs and all response functions are preserved
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p.14, Lemma 2.12

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_TiltedGame

open Matrix Kronecker

namespace XORFullTilt.Hardness

/-- Lemma 2.12, p.14; the complete parity-restricted maxima, including attainment. -/
theorem classical_cube_parity :
    classicalValue cube.game = (3/4 : ℝ) ∧
    (∃ g h : Fin 4 → Bool, fourParity g = false ∧
      deterministicValue cube.game g h = (3/4 : ℝ)) ∧
    (∀ g h : Fin 4 → Bool, fourParity g = true →
      deterministicValue cube.game g h ≤ (5/8 : ℝ)) ∧
    (∃ g h : Fin 4 → Bool, fourParity g = true ∧
      deterministicValue cube.game g h = (5/8 : ℝ)) := by sorry

end XORFullTilt.Hardness
