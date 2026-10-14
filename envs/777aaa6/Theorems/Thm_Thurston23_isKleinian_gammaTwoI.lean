-- Prove2me | Theorems.Thm_Thurston23_isKleinian_gammaTwoI
-- name    : Thurston23.isKleinian_gammaTwoI
-- status  : Proved
-- author  : @t4v1
-- created : 2026-09-13T16:27:40.70036+00:00
-- url     : https://prove2.me/theorems/45b4ad8c-9faa-4d7e-89d4-5a43cf6deed0
-- title:
--   $\Gamma(2+i)$ is a Kleinian group
-- statement:
--   The principal congruence subgroup $\Gamma(2+i)$ of the Picard group $\mathrm{SL}_2(\mathbb{Z}[i])$, acting on hyperbolic $3$-space by Möbius transformations, is a Kleinian group in the sense of the mission bundle: it acts by isometries preserving the hyperbolic volume, freely, and properly discontinuously. Isometry and volume preservation hold for all of $\mathrm{SL}_2(\mathbb{C})$. Proper discontinuity is inherited from the Picard group: a compact set lies in a box $t_0 \le t \le T$, $|q|^2 \le R$, and if $g$ carries a point of the box into the box then $|c q + d|^2 = t/t' \le T/t_0$ bounds the Gaussian integers $c$, $d$, and by the same argument for $g^{-1}$ also $a$ and $b$. Freeness is where the level matters: at a fixed point the trace of $g$ is real and lies in $[-2, 2]$, for $g \in \Gamma(2+i)$ it is congruent to $2$ modulo $2+i$, and the only such Gaussian integer in $[-2, 2]$ is $2$, which forces $g = 1$. The quotient $\mathbb{H}^3/\Gamma(2+i)$ is therefore a hyperbolic $3$-manifold; this is the second milestone's witness, isolated as a reusable statement.
-- source:
--   W. P. Thurston, Three-dimensional manifolds, Kleinian groups and hyperbolic geometry, Bull. Amer. Math. Soc. 6 (1982), 357-381, Question 23 (p. 380). J. Elstrodt, F. Grunewald, J. Mennicke, Groups Acting on Hyperbolic Space, Springer 1998, Chapter 7. Formalisation: https://github.com/t4v1/thurston23/blob/58bb3fd/Thurston23.lean#L1639-L1644.

import Definitions.Def_Thurston23_picard

namespace Thurston23

open MeasureTheory

theorem isKleinian_gammaTwoI : IsKleinian gammaTwoI := by
  sorry

end Thurston23
