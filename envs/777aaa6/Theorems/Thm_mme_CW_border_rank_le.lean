-- Prove2me | Theorems.Thm_mme_CW_border_rank_le
-- name    : mme_CW_border_rank_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-31T17:30:43.059871+00:00
-- url     : https://prove2.me/theorems/80ba3148-ecea-4fd3-bfae-54571f24445f
-- statement:
--   **Border rank of the Coppersmith–Winograd tensor.**
--
--   For every `q ≥ 0`, the CW tensor `T_q` has border rank at most `q + 2`:
--
--   $$\underline R(T_q) \;\leq\; q + 2.$$
--
--   Equivalently, $T_q$ **degenerates** (in the platform's `Degenerates` preorder) from the diagonal unit tensor $I_{q+2}$ — there is a polynomial family of rank-$(q+2)$ tensors whose limit as the deformation parameter goes to $0$ is $T_q$.
--
--   **Construction (the classical CW order-2 degeneration).** Take the polynomial family
--
--   $$\Phi(\varepsilon) \;=\; \frac{1}{\varepsilon^2}\Bigl[\;\sum_{i=1}^{q}\bigl(e_0 + \varepsilon e_i\bigr)^{\otimes 3} \;+\; \bigl(e_0 + \varepsilon^2 e_{q+1}\bigr)^{\otimes 3} \;-\; (q+1)\, e_0^{\otimes 3}\;\Bigr].$$
--
--   Each cube $(e_0 + \varepsilon v)^{\otimes 3}$ has rank $1$, and the explicit expansion in powers of $\varepsilon$ cancels the $\varepsilon^0$ and $\varepsilon^1$ terms; the $\varepsilon^2$ coefficient is precisely $T_q$. So $\Phi(\varepsilon)$ has $q+2$ rank-one terms for every $\varepsilon > 0$ and tends to $T_q$ as $\varepsilon \to 0$ in the *order-2* sense formalised by `DegeneratesOfOrder` in `Def_mme_degeneration`.
--
--   **Why it matters in the CW pipeline.** Combined with Strassen's monotonicity of asymptotic rank under degeneration (`mme_degenerates_asymptoticRank_le`, already Proved), this gives $\widetilde R(T_q) \leq q+2$. For $q = 6$ used by the CW $\omega < 2.376$ bound, this yields the asymptotic-rank upper bound $\widetilde R(T_6) \leq 8$ that feeds into `mme_omega_le_of_subrank_capacity`.
--
--   **Proof status.** Open. The construction is explicit and the proof is mechanical coefficient calculus (~200 lines of Lean), comparable in shape to the existing `mme_schonhage_degenerates`. Will be discharged as a Layer-2 leaf.
-- source:
--   https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_degeneration
open MME
universe u

theorem mme_CW_border_rank_le {K : Type u} [Field K] (q : ℕ) : Degenerates (CWObj K q) (TensorObj.diagObj K 3 (q + 2)) := by sorry
