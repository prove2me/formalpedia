-- Prove2me | Theorems.Thm_XORFullTilt_Hardness_symmetric_structure
-- name    : XORFullTilt.Hardness.symmetric_structure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:53:35.823198+00:00
-- url     : https://prove2.me/theorems/cc221c16-de00-48ac-8af8-2d37b8185f07
-- title:
--   Lemma 4.4 — improved symmetric XOR structure
-- statement:
--   Let $G$ be an XOR game with $|X|=|Y|$ whose constant row and column dual variables $a_x=b_y=\alpha$ are optimal for Eq.(7). Let $C(x,y)=\langle u_x,v_y\rangle$ be an $\varepsilon$-optimal vector correlation, meaning that its bias is at least $\beta^{\rm vect}(G)-2\varepsilon$. Then
--   $$\sum_x\left\|\sum_yH_{x,y}v_y-\alpha u_x\right\|^2\le4(\alpha+4\beta^*(G))\varepsilon,$$
--   $$\sum_y\left\|\sum_xH_{x,y}u_x-\alpha v_y\right\|^2\le4(\alpha+4\beta^*(G))\varepsilon.$$
--   The norms are Euclidean, with sums over questions rather than averages. Both symmetric estimates and the factor two in near-optimality are retained.
--
--   Differences from the source:
--   - encoding: nonnegative approximation error ε → ε is an NNReal, coerced to a real in formulas; reason: this makes the nonnegative-error convention explicit without excluding an admissible error
--   - encoding: real unit vectors and squared Euclidean norms → finite real coordinate vectors and sums of coordinate squares; reason: their spans are finite because the question sets are finite; these are exactly the same squared norms
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p.22, Lemma 4.4

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_VectorDual

open Matrix Kronecker

namespace XORFullTilt.Hardness

/-- Lemma 4.4, p.22; squared Euclidean norms, summed rather than averaged. -/
theorem symmetric_structure {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (G : XORGame X Y)
    (hcard : Fintype.card X = Fintype.card Y) (α : ℝ) (hdual : UniformOptimalBias G α)
    (ε : NNReal) {n : ℕ} (C : VectorCorrelation X Y n)
    (hnear : vectorBias G C ≥ optimalVectorBias G - 2*(ε : ℝ)) :
    (∑ x, ∑ i, ((∑ y, gameMatrix G x y * C.v y i) - α * C.u x i)^2) ≤
      4*(α + 4*quantumBias G)*(ε : ℝ) ∧
    (∑ y, ∑ i, ((∑ x, gameMatrix G x y * C.u x i) - α * C.v y i)^2) ≤
      4*(α + 4*quantumBias G)*(ε : ℝ) := by sorry

end XORFullTilt.Hardness
