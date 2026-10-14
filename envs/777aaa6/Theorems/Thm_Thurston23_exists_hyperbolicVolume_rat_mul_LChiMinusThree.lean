-- Prove2me | Theorems.Thm_Thurston23_exists_hyperbolicVolume_rat_mul_LChiMinusThree
-- name    : Thurston23.exists_hyperbolicVolume_rat_mul_LChiMinusThree
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-11T20:16:20.85668+00:00
-- url     : https://prove2.me/theorems/1521f7ea-9682-4a0d-b64c-95db9bdeb291
-- title:
--   A hyperbolic $3$-manifold whose volume is a rational multiple of $\sqrt{3}\,L(2,\chi_{-3})$
-- statement:
--   Let $F=\mathbb{Q}(\sqrt{-3})$, with discriminant $\delta_F=-3$. Humbert's formula gives the covolume of the Bianchi group $\mathrm{PSL}_2(\mathcal{O}_F)$ as $|\delta_F|^{3/2}\zeta_F(2)/(4\pi^2)$, and with $\zeta_F(s)=\zeta(s)L(s,\chi_{-3})$ this equals
--
--   $$\frac{\sqrt{3}}{8}\,L(2,\chi_{-3}),\qquad L(2,\chi_{-3})=\sum_{n\ge 0}\left(\frac{1}{(3n+1)^2}-\frac{1}{(3n+2)^2}\right)=0.7813024\ldots$$
--
--   Torsion-free subgroups of finite index give honest manifolds: the figure-eight knot complement is the quotient by a torsion-free subgroup of index $12$, and its volume is
--
--   $$\frac{3\sqrt{3}}{2}\,L(2,\chi_{-3})=2.0298832\ldots,$$
--
--   the volume of two regular ideal tetrahedra.
--
--   The statement asserts the consequence: the set of volumes of finite-volume hyperbolic $3$-manifolds, as fixed by the mission bundle, contains a positive rational multiple of $\sqrt{3}\,L(2,\chi_{-3})$.
-- source:
--   W. P. Thurston, Three-dimensional manifolds, Kleinian groups and hyperbolic geometry, Bull. Amer. Math. Soc. 6 (1982), 357-381, Question 23 (p. 380). Volume formula: J. Elstrodt, F. Grunewald, J. Mennicke, Groups Acting on Hyperbolic Space, Springer 1998, Chapter 7, Theorem 1.1, applied to F = Q(sqrt(-3)), where the Bianchi covolume is sqrt(3) L(2, chi_{-3}) / 8 = 0.1691569...; figure-eight knot complement: W. P. Thurston, The Geometry and Topology of Three-Manifolds, Princeton lecture notes 1980, Chapter 1 (decomposition into two regular ideal tetrahedra, volume 2.0298832... = (3 sqrt(3)/2) L(2, chi_{-3})); J. Milnor, Hyperbolic geometry: the first 150 years, Bull. Amer. Math. Soc. 6 (1982), 9-24, section 5.

import Definitions.Def_Thurston23_bundle

namespace Thurston23

open MeasureTheory

theorem exists_hyperbolicVolume_rat_mul_LChiMinusThree :
    ∃ v ∈ hyperbolicVolumes, ∃ q : ℚ, 0 < q ∧
      v = (q : ℝ) * (Real.sqrt 3 *
        ∑' n : ℕ, (1 / ((3 * n + 1) ^ 2 : ℝ) - 1 / ((3 * n + 2) ^ 2 : ℝ))) := by
  sorry

end Thurston23
