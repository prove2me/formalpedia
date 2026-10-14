-- Prove2me | Theorems.Thm_Thurston23_isKleinian_gammaSeven
-- name    : Thurston23.isKleinian_gammaSeven
-- status  : Proved
-- author  : @t4v1
-- created : 2026-09-14T16:23:15.750933+00:00
-- url     : https://prove2.me/theorems/818ce231-4bd3-4984-a08b-97105da439dd
-- title:
--   $\Gamma(3+\omega)$ is a Kleinian group
-- statement:
--   The principal congruence subgroup $\Gamma(3+\omega)$ of the Bianchi group $\mathrm{SL}_2(\mathbb{Z}[\omega])$, $\omega = e^{2\pi i/3}$, acting on hyperbolic $3$-space by Möbius transformations, is a Kleinian group in the sense of the mission bundle: it acts by isometries preserving the hyperbolic volume, freely, and properly discontinuously. Proper discontinuity holds for the whole Bianchi group, because elements moving a compact set to meet itself have entries in a bounded disc, which contains finitely many Eisenstein integers. Freeness uses the level: $3+\omega$ is a prime of norm $7$, at a fixed point the trace is a rational integer in $[-2,2]$ congruent to $2$ modulo $3+\omega$, hence equal to $2$, which forces the identity. The quotient $\mathbb{H}^3/\Gamma(3+\omega)$ is therefore a hyperbolic $3$-manifold.
-- source:
--   W. P. Thurston, Three-dimensional manifolds, Kleinian groups and hyperbolic geometry, Bull. Amer. Math. Soc. 6 (1982), 357-381, Question 23 (p. 380). J. Elstrodt, F. Grunewald, J. Mennicke, Groups Acting on Hyperbolic Space, Springer 1998, Chapter 7 (Bianchi groups and Humbert's formula). Formalisation: https://github.com/t4v1/thurston23/blob/main/Thurston23Eisenstein.lean (isKleinian_gammaSeven).

import Definitions.Def_Thurston23_eisenstein

namespace Thurston23

open MeasureTheory

theorem isKleinian_gammaSeven : IsKleinian gammaSeven := by
  sorry

end Thurston23
