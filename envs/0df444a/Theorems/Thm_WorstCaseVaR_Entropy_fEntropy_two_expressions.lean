-- Prove2me | Theorems.Thm_WorstCaseVaR_Entropy_fEntropy_two_expressions
-- name    : WorstCaseVaR.Entropy.fEntropy_two_expressions
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:17:30.545995+00:00
-- url     : https://prove2.me/theorems/bf5215da-a30d-4ae2-a517-4a532c1361ff
-- title:
--   Eq. (45), p. 553 — the two expressions of f(ε, d) agree
-- statement:
--   For real numbers $\varepsilon$ and $d$, the two suprema defining $f(\varepsilon,d)$ in Eq. (45) coincide:
--   $$\sup_{\lambda > 0} \frac{e^{\varepsilon/\lambda - d} - 1}{e^{1/\lambda} - 1} \;=\; \sup_{v > 0} \frac{e^{-d}(v+1)^{\varepsilon} - 1}{v}.$$
--
--   The second expression is the one convenient for numerical evaluation of the risk factor $\kappa(\varepsilon,d)$ of Theorem 9.
--
--   **Formalization Note** Both sides are Lean `sSup`s of images of $(0,\infty)$; $(v+1)^\varepsilon$ is the real power with positive base.
-- source:
--   El Ghaoui, Oks and Oustry, Worst-Case Value-at-Risk and Robust Portfolio Optimization: A Conic Programming Approach, Oper. Res. 51 (2003), p. 553, Theorem 9, Eq. (45)

import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

namespace WorstCaseVaR.Entropy

/-- Eq. (45), p. 553: the two expressions of `f(ε, d)` agree,
`sup_{λ>0} (e^{ε/λ-d} - 1)/(e^{1/λ} - 1) = sup_{v>0} (e^{-d}(v + 1)^ε - 1)/v`. -/
theorem fEntropy_two_expressions (ε d : ℝ) :
    fEntropy ε d =
      sSup ((fun v : ℝ => (Real.exp (-d) * (v + 1) ^ ε - 1) / v) '' Set.Ioi 0) := by sorry

end WorstCaseVaR.Entropy
