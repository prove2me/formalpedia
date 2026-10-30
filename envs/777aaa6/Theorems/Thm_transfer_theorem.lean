-- Prove2me | Theorems.Thm_transfer_theorem
-- name    : transfer_theorem
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:43:28.068967+00:00
-- url     : https://prove2.me/theorems/bc780da6-915e-476e-80fc-52c65d7044c0
-- title:
--   Algebraic delta-domain coefficient transfer
-- statement:
--   Let $\alpha,C\in\mathbb C$, with $C\ne0$ and $\alpha\notin\{0,-1,-2,\ldots\}$. Let $R>1$ and $0<\varphi<\pi/2$, and write $\Delta=\{z:|z|<R,\ \varphi<|\arg(z-1)|\}$. Suppose $f$ has the specified Taylor series $p$ at zero and is analytic on a neighborhood of every point of $\Delta$. If, as $z\to1$ within $\Delta$, $|f(z)-C(1-z)^{-\alpha}|\,|1-z|^{\operatorname{Re}\alpha}\to0$, then, as natural $n\to\infty$,
--
--   $$p.\mathrm{coeff}(n)\sim \frac{C n^{\alpha-1}}{\Gamma_{\mathbb C}(\alpha)}.$$
--
--    Complex powers use the principal branch. No restriction on $\operatorname{Re}\alpha$ or coefficient positivity is added.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/TransferGeneral.lean#L71. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_DeltaDomain
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# General singularity-analysis transfer theorem

This file assembles the general Darboux little-o transfer estimate with the
standard coefficient scale for `(1 - z)^{-α}`. Unlike the restricted theorem,
there is no lower bound on `α.re`; the only exclusion is that `α` is not a
nonpositive integer, exactly the hypothesis needed for the standard scale.
-/

open Complex Filter Asymptotics
open scoped Topology BigOperators

theorem transfer_theorem {α C : ℂ} {R φ : ℝ} {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hα : ∀ m : ℕ, α ≠ -m) (hC : C ≠ 0) (hR : 1 < R) (hφ0 : 0 < φ)
    (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p 0)
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hsing : Tendsto
      (fun z : ℂ => ‖f z - C * (1 - z) ^ (-α)‖ * ‖(1 : ℂ) - z‖ ^ (α.re))
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => C * (n : ℂ) ^ (α - 1) / Complex.Gamma α) := by sorry
