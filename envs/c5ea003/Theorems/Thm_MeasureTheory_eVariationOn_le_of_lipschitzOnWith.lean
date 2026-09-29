-- Prove2me | Theorems.Thm_MeasureTheory_eVariationOn_le_of_lipschitzOnWith
-- name    : MeasureTheory.eVariationOn_le_of_lipschitzOnWith
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:19:00.683063+00:00
-- url     : https://prove2.me/theorems/b3ce57cf-8718-4e32-afa7-12803d6872a3
-- title:
--   The variation of a Lipschitz curve on an interval is at most C times its length
-- statement:
--   If $f:\mathbb{R}\to F$ is $C$-Lipschitz on $[a,b]$ with $a\le b$, then its total variation there is at most $C(b-a)$:
--   $$V_a^b(f)\ \le\ C\,(b-a).$$
--
--   **Role.** This is the elementary length bound for a rectifiable curve: a Lipschitz parametrisation has length at most its Lipschitz constant times the length of the parameter interval. Mathlib records how the variation behaves under composition with a Lipschitz map and bounds the variation of a monotone real function, but not this combination, which is the form one actually uses when estimating the length of a curve. In the theory of harmonic maps into buildings it bounds the length of the image of a coordinate circle from above by the angular speed of the parametrisation, one half of the identity $\ell(u(\mathbb{S}^1))=2\pi\alpha L$ in the constant-distance case.
--
--   **The argument.** Composing with the identity, the variation of $f$ on $[a,b]$ is at most $C$ times the variation of the identity map there; the identity is monotone, so its variation on $[a,b]$ is at most $b-a$. Multiplying out, and noting that a nonnegative real constant passes through the map $\mathbb{R}\to[0,\infty]$, gives the bound.
-- source:
--   Standard; combines MeasureTheory.LipschitzOnWith.comp_eVariationOn_le and MonotoneOn.eVariationOn_le of Mathlib (Mathlib.Topology.EMetricSpace.BoundedVariation).

import Mathlib

namespace MeasureTheory

universe u

theorem eVariationOn_le_of_lipschitzOnWith {F : Type u} [PseudoEMetricSpace F]
    (f : ℝ → F) (C : NNReal) (a b : ℝ) (hab : a ≤ b)
    (hf : LipschitzOnWith C f (Set.Icc a b)) :
    eVariationOn f (Set.Icc a b) ≤ ENNReal.ofReal (C * (b - a)) := by sorry

end MeasureTheory
