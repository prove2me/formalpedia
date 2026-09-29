-- Prove2me | Theorems.Thm_TalagrandCore_kr_lower_tail
-- name    : TalagrandCore.kr_lower_tail
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T04:59:50.625873+00:00
-- url     : https://prove2.me/theorems/72e88a90-a6eb-4adc-aa88-dfcaffc4cc72
-- title:
--   Klein–Rio lower tail for a finite Bernoulli linear supremum
-- statement:
--   Assume the unit coefficient envelope, a variance bound by $w>0$, and $\mathbb EZ\le w$. Then for every $u\ge0$,
--
--   $$
--   \mathbb P\{Z\le\mathbb EZ-u\}
--   \le \exp\!\left(-\frac{u}{32}\log\left(1+\frac{u}{w}\right)\right).
--   $$
--
--   This combines the compensated-process cumulant estimate near the origin with a single-branch Bennett bound in the far regime.
--
--   **Formalization Note** The theorem is specialized to a finite class and a finite Bernoulli product space.
-- source:
--   T. Klein and E. Rio, Concentration around the mean for maxima of empirical processes, Annals of Probability 33 (2005), Sections 2 and 4, pp. 1060–1077, arXiv:math/0506594. Formal Lean proof extracted from Prove2Me accepted submission bf106d23-ff42-48f5-a837-a8528101c849 by tianyipeng.

import Definitions.Def_talagrand_finite_bool_core
open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem kr_lower_tail (p : NNReal) (hp : p ≤ 1) (coeff : ι → κ → ℝ)
    (hB : ∀ a x, |coeff a x| ≤ 1) {w : ℝ} (hw : 0 < w)
    (hVar : ∀ a, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ w)
    (hEZ : Ex (p : ℝ) (Zproc coeff (p : ℝ)) ≤ w)
    {u : ℝ} (hu : 0 ≤ u) :
    Ex (p : ℝ) (fun ω => if Zproc coeff (p : ℝ) ω ≤ Ex (p : ℝ) (Zproc coeff (p : ℝ)) - u then (1:ℝ) else 0) ≤
      Real.exp (-((u / 32) * Real.log (1 + u / w))) := by sorry

end TalagrandCore
