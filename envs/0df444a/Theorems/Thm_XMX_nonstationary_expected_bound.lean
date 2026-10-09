-- Prove2me | Theorems.Thm_XMX_nonstationary_expected_bound
-- name    : XMX.nonstationary_expected_bound
-- status  : Open
-- author  : @visuddhi
-- created : 2026-10-08T17:03:07.52395+00:00
-- url     : https://prove2.me/theorems/ad1655c4-c79e-44f8-918f-162f7a5a4c96
-- title:
--   Xie–Ma–Xin Corollary 4.10: expected EE and GE bound
-- statement:
--   There is one absolute C>0 such that for every positive T,N,U, lead time L>=0, h,b in [0,1], and joint demand law, expected one-sided GE is at most C(L+1)U/sqrt(N). Expected ERM excess risk relative to a population minimizer is no larger than expected GE for every empirical selector with integrable selected risk. Loss is the average over the final T periods; K=0. No independence across periods is imposed.
-- source:
--   Yaqi Xie, Will Ma, Linwei Xin, VC Theory for Inventory Policies, arXiv:2404.11509v3 (2026-02-01), Corollary 4.10, Sections 3.1 and 8.6

import Definitions.Def_XMX_NonstationaryInventory
import Definitions.Def_XMX_CyclicPartition

set_option autoImplicit false
open MeasureTheory

namespace XMX

theorem nonstationary_expected_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (T L N : ℕ), 0 < T → 0 < N →
      ∀ (U h b : ℝ), 0 < U → h ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (μ : Measure (Demand T L U)) [IsProbabilityMeasure μ],
      expectedGE N μ (loss T L U h b) ≤ C * (((L : ℝ) + 1) * U) / Real.sqrt N ∧
      ∀ (select : (Fin N → Demand T L U) → Levels T L U)
        (pstar : Levels T L U),
        (∀ data p, empiricalRisk N (loss T L U h b) data (select data) ≤
          empiricalRisk N (loss T L U h b) data p) →
        (∀ p, risk μ (loss T L U h b) pstar ≤ risk μ (loss T L U h b) p) →
        Integrable (fun data => risk μ (loss T L U h b) (select data))
          (Measure.pi (fun _ : Fin N => μ)) →
        expectedEE N μ (loss T L U h b) select pstar ≤
          expectedGE N μ (loss T L U h b) := by sorry

end XMX
