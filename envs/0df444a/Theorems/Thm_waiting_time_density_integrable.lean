-- Prove2me | Theorems.Thm_waiting_time_density_integrable
-- name    : waiting_time_density_integrable
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T22:11:59.51527+00:00
-- url     : https://prove2.me/theorems/501bde87-18ee-4c70-8a98-3cca25fa74cf
-- title:
--   Integrability of the waiting-time density
-- statement:
--   **Integrability of the waiting-time density.** The order-statistic waiting-time density $f(s)=N\binom{N-1}{m_p}(1-e^{-\lambda s})^{m_p}(e^{-\lambda s})^{N-m_p}\lambda$ ($m_p<N$, $\lambda>0$) is integrable on $(0,\infty)$. It is dominated by $C\,e^{-\lambda s}$ since $(1-e^{-\lambda s})^{m_p}\le 1$ and $(e^{-\lambda s})^{N-m_p}\le e^{-\lambda s}$ (as $N-m_p\ge 1$); `integrableOn_exp_mul_Ioi` and `Integrable.mono'` finish. Source: Siegel (2001), Thm 2.2.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
open MeasureTheory Set

theorem waiting_time_density_integrable (N mp : ℕ) (lam : ℝ) (h : mp < N) (hlam : 0 < lam) :
    MeasureTheory.IntegrableOn
      (fun s => (N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * s))) ^ mp
        * (Real.exp (-(lam * s))) ^ (N - mp) * lam) (Set.Ioi (0:ℝ)) := by sorry
