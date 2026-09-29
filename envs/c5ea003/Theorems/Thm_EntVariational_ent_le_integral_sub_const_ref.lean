-- Prove2me | Theorems.Thm_EntVariational_ent_le_integral_sub_const_ref
-- name    : EntVariational.ent_le_integral_sub_const_ref
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T04:18:40.342908+00:00
-- url     : https://prove2.me/theorems/f27185fd-c786-405a-9ded-03ca42d7c236
-- title:
--   BLM Theorem 4.13: variational upper bound on the entropy functional
-- statement:
--   Variational (dual) upper bound on the entropy functional with a constant reference (Boucheron–Lugosi–Massart, *Concentration Inequalities*, OUP 2013, Theorem 4.13). For a probability measure $\mu$, a nonnegative integrable $Y$ whose $Y\log Y$ is integrable, and any positive constant $u$, the entropy $\mathrm{Ent}_\mu(Y)=\int Y\log Y\,d\mu-(\int Y\,d\mu)\log(\int Y\,d\mu)$ is bounded above by $\int (Y\log Y - Y\log u - (Y-u))\,d\mu$, with equality at $u=\int Y\,d\mu$.
-- source:
--   Boucheron, Lugosi, Massart, Concentration Inequalities (OUP 2013), Theorem 4.13 (duality/variational formula of entropy), upper-bound half; used conditionally in Theorem 6.6 (modified log-Sobolev inequality).

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
open Real MeasureTheory

namespace EntVariational
theorem ent_le_integral_sub_const_ref
    {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [IsProbabilityMeasure μ] {Y : α → ℝ} {u : ℝ}
    (hY_nonneg : ∀ x, 0 ≤ Y x)
    (hY_int : Integrable Y μ)
    (hYlog_int : Integrable (fun x ↦ Y x * Real.log (Y x)) μ)
    (hu : 0 < u) :
    (∫ x, Y x * Real.log (Y x) ∂μ) - (∫ x, Y x ∂μ) * Real.log (∫ x, Y x ∂μ)
      ≤ ∫ x, (Y x * Real.log (Y x) - Y x * Real.log u - (Y x - u)) ∂μ := by sorry
end EntVariational
