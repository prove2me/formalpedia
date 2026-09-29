-- Prove2me | Theorems.Thm_TalagrandCore_kr_coordinate_cgf_bennett_explicit
-- name    : TalagrandCore.kr_coordinate_cgf_bennett_explicit
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T05:49:51.575247+00:00
-- url     : https://prove2.me/theorems/d34efbd7-2554-4696-8b05-0feeda64c0fa
-- title:
--   Explicit coordinate-sum Bennett bound for a Bernoulli branch
-- statement:
--   Let $\kappa$ be a finite coordinate set and let $a$ be one branch of a finite centered Bernoulli linear class. Suppose every coefficient has absolute value at most one and the total variance is at most $\sigma^2$. If $\ell_x(t)$ is the exact one-coordinate negative cumulant, then for every $t\ge0$,
--
--   $$
--   \sum_{x\in\kappa}\ell_x(t)\le\sigma^2(e^t-t-1).
--   $$
--
--   This is the additive Bennett estimate used in the far lower-tail argument.
--
--   **Formalization Note** All type and scalar parameters are explicit, and `krl` is the logarithm of the exact Bernoulli coordinate MGF.
-- source:
--   T. Klein and E. Rio, Concentration around the mean for maxima of empirical processes, Annals of Probability 33 (2005), Lemma 4.4 and Section 4, pp. 1060–1077, arXiv:math/0506594. Formal Lean proof extracted from accepted submission bf106d23-ff42-48f5-a837-a8528101c849 by tianyipeng.

import Definitions.Def_talagrand_finite_bool_core
open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

theorem kr_coordinate_cgf_bennett_explicit (κ ι : Type) [DecidableEq κ] [Fintype κ]
    [Fintype ι] [Nonempty ι] (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (coeff : ι → κ → ℝ) (a : ι) (hB : ∀ x, |coeff a x| ≤ 1) (sigmaSq : ℝ)
    (hVar : ∑ x : κ, p * (1 - p) * coeff a x ^ 2 ≤ sigmaSq) (t : ℝ) (ht : 0 ≤ t) :
    (∑ x : κ, krl coeff p a x t) ≤ sigmaSq * (Real.exp t - t - 1) := by sorry

end TalagrandCore
