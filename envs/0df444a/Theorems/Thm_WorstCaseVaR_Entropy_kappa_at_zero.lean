-- Prove2me | Theorems.Thm_WorstCaseVaR_Entropy_kappa_at_zero
-- name    : WorstCaseVaR.Entropy.kappa_at_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:20:40.886714+00:00
-- url     : https://prove2.me/theorems/833a5975-e9b8-4f69-9e58-1c7e4b00fe2d
-- title:
--   Remark after Theorem 9, p. 553 — f(ε, 0) = ε, κ(ε, 0) = −Φ⁻¹(ε), and κ(ε, d) increases with d
-- statement:
--   For $0 < \varepsilon < 1$,
--   $$f(\varepsilon, 0) = \sup_{\lambda > 0}\frac{e^{\varepsilon/\lambda} - 1}{e^{1/\lambda} - 1} = \varepsilon, \qquad\text{hence}\qquad \kappa(\varepsilon, 0) = -\Phi^{-1}(\varepsilon).$$
--
--   With $d = 0$ the relative-entropy class is the single Gaussian $P_0 = \mathcal N(\hat x, \Gamma)$, and Theorem 9 then recovers the classical Gaussian Value-at-Risk with risk factor $-\Phi^{-1}(\varepsilon)$.
--
--   Moreover the risk factor $\kappa(\varepsilon, d) = -\Phi^{-1}(f(\varepsilon, d))$ is strictly increasing in $d \ge 0$: as the class of allowable distributions grows, the worst-case VaR increases.
--
--   **Formalization Note** The paper's range is $\varepsilon \in (0,1]$; the statement is made for $0 < \varepsilon < 1$, the range of the mission. The paper's "increases with d" is read as strict increase on $d \in [0, \infty)$ (`StrictMonoOn`), which holds because $f(\varepsilon, \cdot)$ is strictly decreasing with values in $(0, 1)$ there.
-- source:
--   El Ghaoui, Oks and Oustry, Worst-Case Value-at-Risk and Robust Portfolio Optimization: A Conic Programming Approach, Oper. Res. 51 (2003), p. 553, remark after Theorem 9

import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

namespace WorstCaseVaR.Entropy

/-- Remark after Theorem 9, p. 553: for `d = 0`, `f(ε, 0) = ε` and hence
`κ(ε, 0) = -Φ⁻¹(ε)`; and the risk factor `κ(ε, d)` increases with `d ≥ 0`. -/
theorem kappa_at_zero (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    fEntropy ε 0 = ε ∧ kappaEntropy ε 0 = -normalQuantile ε ∧
      StrictMonoOn (kappaEntropy ε) (Set.Ici 0) := by sorry

end WorstCaseVaR.Entropy
