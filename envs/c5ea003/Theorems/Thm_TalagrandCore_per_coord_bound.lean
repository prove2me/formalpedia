-- Prove2me | Theorems.Thm_TalagrandCore_per_coord_bound
-- name    : TalagrandCore.per_coord_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T04:58:52.544617+00:00
-- url     : https://prove2.me/theorems/0e146a27-b018-4f34-a2b3-f10db66f7425
-- title:
--   One-coordinate two-copy entropy bound
-- statement:
--   Let $V$ be a function on a finite Bernoulli cube whose change under resampling one coordinate is bounded by one and whose squared change is controlled by a nonnegative variance function $u$. Then the two Bernoulli branches of the entropy kernel at that coordinate satisfy the corresponding weighted quadratic-exponential bound.
--
--   $$
--   \sum_{b\in\{0,1\}}w_b\,\mathbb E\!\left[e^{\lambda V}\psi\!\left(\lambda(V-V^{x\leftarrow b})\right)\right]
--   \le \frac{\lambda^2}{2}e^\lambda(1+e^\lambda)\,\mathbb E[e^{\lambda V}U_x].
--   $$
--
--   This is the reusable one-coordinate core of the two-copy argument.
--
--   **Formalization Note** The exact expression $U_x$ is the Bernoulli-weighted variance term in the formal statement.
-- source:
--   Michel Ledoux, On Talagrand’s deviation inequalities for product measures, ESAIM Probability and Statistics 1 (1996), Theorems 2.4–2.5, pp. 63–87. Formal Lean proof extracted from Prove2Me accepted submission bf106d23-ff42-48f5-a837-a8528101c849 by tianyipeng.

import Definitions.Def_talagrand_finite_bool_core
open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem per_coord_bound (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (V u : (κ → Bool) → ℝ) (x : κ)
    (hu : ∀ ω, 0 ≤ u ω)
    (hD1 : ∀ ω t, |V ω - V (Function.update ω x t)| ≤ 1)
    (hDsq : ∀ ω t, (V ω - V (Function.update ω x t)) ^ 2 ≤
        (cond (ω x) (1:ℝ) 0 - cond t 1 0) ^ 2 * (u ω + u (Function.update ω x t))) :
    bw q true * Ex q (fun ω => Real.exp (lam * V ω) *
        psi (lam * (V ω - V (Function.update ω x true)))) +
      bw q false * Ex q (fun ω => Real.exp (lam * V ω) *
        psi (lam * (V ω - V (Function.update ω x false)))) ≤
      lam ^ 2 / 2 * Real.exp lam * (1 + Real.exp lam) *
        Ex q (fun ω => Real.exp (lam * V ω) *
          (u ω * ((cond (ω x) (1:ℝ) 0 - q) ^ 2 + q * (1 - q)))) := by sorry

end TalagrandCore
