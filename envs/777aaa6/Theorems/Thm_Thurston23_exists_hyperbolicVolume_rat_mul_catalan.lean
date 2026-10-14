-- Prove2me | Theorems.Thm_Thurston23_exists_hyperbolicVolume_rat_mul_catalan
-- name    : Thurston23.exists_hyperbolicVolume_rat_mul_catalan
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-11T20:16:29.094983+00:00
-- url     : https://prove2.me/theorems/fa44c278-c068-41e4-8fce-3bec1b41cf81
-- title:
--   A hyperbolic $3$-manifold whose volume is a rational multiple of Catalan's constant
-- statement:
--   Let $F=\mathbb{Q}(i)$, with ring of integers $\mathbb{Z}[i]$ and discriminant $\delta_F=-4$. Humbert's formula expresses the covolume of the Bianchi group $\mathrm{PSL}_2(\mathbb{Z}[i])$, acting on hyperbolic $3$-space, as
--
--   $$\frac{|\delta_F|^{3/2}\,\zeta_F(2)}{4\pi^2},$$
--
--   and since $\zeta_F(s)=\zeta(s)L(s,\chi_{-4})$ for this field, that covolume equals $G/3$, where
--
--   $$G=\sum_{n\ge 0}\frac{(-1)^n}{(2n+1)^2}=0.9159655\ldots$$
--
--   is Catalan's constant. The Bianchi group itself has torsion, so its quotient is an orbifold rather than a manifold; but it contains torsion-free subgroups of finite index, for instance the principal congruence subgroup of level $2+i$, and the quotient by such a subgroup is a finite-volume hyperbolic $3$-manifold whose volume is the index times $G/3$.
--
--   The statement asserts exactly this consequence: the set of volumes of finite-volume hyperbolic $3$-manifolds, as fixed by the mission bundle (measures of fundamental domains of Kleinian actions on the upper half-space with density $z^{-3}$), contains a positive rational multiple of Catalan's constant.
-- source:
--   W. P. Thurston, Three-dimensional manifolds, Kleinian groups and hyperbolic geometry, Bull. Amer. Math. Soc. 6 (1982), 357-381, Question 23 (p. 380). Volume formula: G. Humbert, Sur la mesure des classes d'Hermite de discriminant donne dans un corps quadratique imaginaire, C. R. Acad. Sci. Paris 169 (1919), 448-454; J. Elstrodt, F. Grunewald, J. Mennicke, Groups Acting on Hyperbolic Space, Springer 1998, Chapter 7, Theorem 1.1 (covolume of the Bianchi group of an imaginary quadratic field F equals |delta_F|^{3/2} zeta_F(2) / (4 pi^2)); for F = Q(i) this equals Catalan's constant divided by 3.

import Definitions.Def_Thurston23_bundle

namespace Thurston23

open MeasureTheory

theorem exists_hyperbolicVolume_rat_mul_catalan :
    ∃ v ∈ hyperbolicVolumes, ∃ q : ℚ, 0 < q ∧
      v = (q : ℝ) * ∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ) := by
  sorry

end Thurston23
