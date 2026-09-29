-- Prove2me | Theorems.Thm_TalagrandCore_poisson_tail
-- name    : TalagrandCore.poisson_tail
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T04:59:09.143874+00:00
-- url     : https://prove2.me/theorems/fe0f7271-ba21-4a56-bdcf-7b90913e709c
-- title:
--   Poisson tail for a nonnegative self-bounding supremum
-- statement:
--   Let $Y$ be a finite supremum process with summands in $[0,1]$. If $\mathbb EY\le m\le s$ and $m>0$, then
--
--   $$
--   \mathbb P\{Y\ge s\}\le
--   \exp\!\left(-s\log\frac{s}{m}+s-m\right).
--   $$
--
--   This is the Chernoff consequence of the self-bounding exponential-moment estimate.
--
--   **Formalization Note** Probabilities are represented as expectations of indicator functions.
-- source:
--   Michel Ledoux, On Talagrand’s deviation inequalities for product measures, ESAIM Probability and Statistics 1 (1996), Theorems 2.4–2.5, pp. 63–87. Formal Lean proof extracted from Prove2Me accepted submission bf106d23-ff42-48f5-a837-a8528101c849 by tianyipeng.

import Definitions.Def_talagrand_finite_bool_core
open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem poisson_tail (p : NNReal) (hp : p ≤ 1)
    (g : ι → κ → Bool → ℝ) (hg0 : ∀ a x b, 0 ≤ g a x b)
    (hg1 : ∀ a x b, g a x b ≤ 1) {m s : ℝ}
    (hm : Ex (p : ℝ) (fun ω => supProc g ω) ≤ m) (hm0 : 0 < m) (hms : m ≤ s) :
    Ex (p : ℝ) (fun ω => if s ≤ supProc g ω then (1:ℝ) else 0) ≤
      Real.exp (-(s * Real.log (s / m) - s + m)) := by sorry

end TalagrandCore
