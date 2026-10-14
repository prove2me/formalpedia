-- Prove2me | Theorems.Thm_Thurston23_isFundamentalDomain_eisBox
-- name    : Thurston23.isFundamentalDomain_eisBox
-- status  : Proved
-- author  : @t4v1
-- created : 2026-09-14T16:22:58.212795+00:00
-- url     : https://prove2.me/theorems/653c289a-ac96-4ffd-bd6c-61286cf96e80
-- title:
--   The box over a rhombus is a fundamental domain for the Bianchi group $\mathrm{PSL}_2(\mathbb{Z}[\omega])$
-- statement:
--   The box
--
--   $$B = \{(x,y,t) : 0 \le x \le \tfrac12,\ 0 \le x + \sqrt3\,y \le 1,\ x^2 + y^2 + t^2 \ge 1\}$$
--
--   is a fundamental domain, in the sense of Mathlib's `MeasureTheory.IsFundamentalDomain`, for the Bianchi group $\mathrm{SL}_2(\mathbb{Z}[\omega])$ modulo the kernel of its action on hyperbolic $3$-space. The rhombus $\{0 \le x \le \tfrac12,\ 0 \le x + \sqrt3 y \le 1\}$ is a third of the hexagonal Voronoi cell of the lattice $\mathbb{Z}[\omega]$, and so a fundamental domain for its translations together with the rotations by $\omega$. Every orbit meets $B$ (a point of maximal height, translated to the Voronoi cell of $0$, lies above the unit sphere, and a rotation by a power of $\omega$ brings it over the rhombus); an element carrying a point of the interior of $B$ into the interior acts trivially; and the boundary of $B$ has volume zero. Consequently the hyperbolic volume of $B$ is the covolume of $\mathrm{PSL}_2(\mathbb{Z}[\omega])$.
-- source:
--   W. P. Thurston, Three-dimensional manifolds, Kleinian groups and hyperbolic geometry, Bull. Amer. Math. Soc. 6 (1982), 357-381, Question 23 (p. 380). J. Elstrodt, F. Grunewald, J. Mennicke, Groups Acting on Hyperbolic Space, Springer 1998, Chapter 7 (Bianchi groups and Humbert's formula). Formalisation: https://github.com/t4v1/thurston23/blob/main/Thurston23Eisenstein.lean (isFundamentalDomain_eisBox).

import Definitions.Def_Thurston23_eisenstein

namespace Thurston23

open MeasureTheory

theorem isFundamentalDomain_eisBox :
    MeasureTheory.IsFundamentalDomain EisEff eisBox hvol := by
  sorry

end Thurston23
