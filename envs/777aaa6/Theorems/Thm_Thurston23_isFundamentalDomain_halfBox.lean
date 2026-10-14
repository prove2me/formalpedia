-- Prove2me | Theorems.Thm_Thurston23_isFundamentalDomain_halfBox
-- name    : Thurston23.isFundamentalDomain_halfBox
-- status  : Proved
-- author  : @t4v1
-- created : 2026-09-13T16:27:47.617331+00:00
-- url     : https://prove2.me/theorems/528a6e05-bed3-48e0-8513-48f5b7e2b6be
-- title:
--   The half box is a fundamental domain for the Picard group acting effectively
-- statement:
--   The closed half box
--
--   $$B = \{(x,y,t) : |x| \le \tfrac12,\ 0 \le y \le \tfrac12,\ x^2 + y^2 + t^2 \ge 1\}$$
--
--   is a fundamental domain, in the sense of Mathlib's `MeasureTheory.IsFundamentalDomain`, for the Picard group $\mathrm{SL}_2(\mathbb{Z}[i])$ modulo the kernel $\{\pm 1\}$ of its action on hyperbolic $3$-space. This is the three-dimensional analogue of the modular domain of $\mathrm{SL}_2(\mathbb{Z})$: every orbit meets $B$ (reduction theory for $\mathbb{Z}[i]$: take a point of maximal height on the orbit, translate it into $|x|, |y| \le \tfrac12$, and note that the inversion would raise the height if $|q| < 1$; then fold $y < 0$ onto $y > 0$ by $z \mapsto -z$); an element carrying a point of the open box into the open box acts trivially (comparing heights forces $c = 0$, and the remaining upper triangular element must be $\pm 1$); and the boundary of $B$, contained in four coordinate planes and the unit sphere, has hyperbolic volume zero. Consequently the hyperbolic volume of $B$ is the covolume of $\mathrm{PSL}_2(\mathbb{Z}[i])$.
-- source:
--   W. P. Thurston, Three-dimensional manifolds, Kleinian groups and hyperbolic geometry, Bull. Amer. Math. Soc. 6 (1982), 357-381, Question 23 (p. 380). J. Elstrodt, F. Grunewald, J. Mennicke, Groups Acting on Hyperbolic Space, Springer 1998, Chapter 7, Section 1 (the fundamental domain of the Picard group). Formalisation: https://github.com/t4v1/thurston23/blob/58bb3fd/Thurston23.lean#L2816-L2859 (section PicardFundamentalDomain).

import Definitions.Def_Thurston23_picard

namespace Thurston23

open MeasureTheory

theorem isFundamentalDomain_halfBox :
    MeasureTheory.IsFundamentalDomain PicardEff halfBox hvol := by
  sorry

end Thurston23
