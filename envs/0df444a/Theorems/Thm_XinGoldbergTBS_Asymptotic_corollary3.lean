-- Prove2me | Theorems.Thm_XinGoldbergTBS_Asymptotic_corollary3
-- name    : XinGoldbergTBS.Asymptotic.corollary3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:27:56.923506+00:00
-- url     : https://prove2.me/theorems/bd23f253-8e42-4353-a6ba-55164a6d4ea8
-- title:
--   Corollary 3 — $\mathrm{OPT}(L)$ lower bound through the random walk maxima $Z^{r_L}_k$
-- statement:
--   For $L_0 \ge 0$, $L > L_0 + 1$, $\alpha\in(0,1)$, and every witness of Theorem 2 with $r_L = \mathbb E[\chi^{*,L}_1]$, writing $S_{\alpha,L} = S^\infty_\alpha(r_L)$:
--   $$\mathrm{OPT}(L) \ge c(\mathbb E[D]-r_L) + (1-\alpha)\sum_{k=1}^\infty\alpha^{k-1}\,\mathbb E\Big[G\Big(S_{\alpha,L} + Z^{r_L}_k - \sum_{i=1}^{L_0+1}(D'_i - r_L)\Big)\Big] - U_0(1-\alpha)^{-3}L\alpha^{L-L_0},$$
--   where $Z^{r_L}_k = \max_{i\in[0,k-1]}W^{r_L}_i$ is built from demands independent of the i.i.d. copies $D'_1, \dots, D'_{L_0+1}$ of $D$.
--
--   This expresses the lower bound through the inventory process of a base-stock policy, which is then compared with the TBS cost formula (3).
--
--   **Formalization Note** The subtracted term is moved to the left-hand side (all terms in $[0,\infty]$), and the summation index is shifted by one ($k \mapsto k+1$).
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 444, Corollary 3

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Constants
import Definitions.Def_XinGoldbergTBS_Asymptotic_RandomWalk
import Definitions.Def_XinGoldbergTBS_Asymptotic_SingleSource
import Definitions.Def_XinGoldbergTBS_Asymptotic_Witness

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- Corollary 3, p. 444, for every witness of Theorem 2, with `S_{α,L} = S^∞_α(r_L)` and
`Z^{r_L}_k` independent of `D'_1, …, D'_{L₀+1}` (the subtracted term moved to the left side;
summation index `k` here is the paper's `k + 1`). -/
theorem corollary3 (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ) (I : Ω → ℝ) (D : ℕ → Ω → ℝ)
    (hw : IsStationaryWitness P μ κ L₀ L χ q I D)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal (κ.c * (μ.mean - rL P L₀ L χ)) +
        ENNReal.ofReal (1 - α) *
          ∑' k : ℕ, ENNReal.ofReal (α ^ k) *
            ∫⁻ p : Path × (Fin (L₀ + 1) → ℝ),
              ENNReal.ofReal (G κ (Sinf μ κ L₀ α (rL P L₀ L χ) + Z (rL P L₀ L χ) p.1 (k + 1)
                - ∑ i, (p.2 i - rL P L₀ L χ)))
              ∂((pathLaw μ).prod (sumLaw μ L₀))
      ≤ OPT μ κ L₀ L +
        ENNReal.ofReal (U0 μ κ L₀ * ((1 - α) ^ 3)⁻¹ * L * α ^ (L - L₀)) := by sorry

end XinGoldbergTBS.Asymptotic
