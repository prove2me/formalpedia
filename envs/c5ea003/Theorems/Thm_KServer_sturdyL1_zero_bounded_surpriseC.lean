-- Prove2me | Theorems.Thm_KServer_sturdyL1_zero_bounded_surpriseC
-- name    : KServer.sturdyL1_zero_bounded_surpriseC
-- status  : Open
-- author  : @WillR
-- created : 2026-10-02T17:08:29.676988+00:00
-- url     : https://prove2.me/theorems/b6abd7a2-3ec1-449b-9e3c-1545555dede0
-- title:
--   Zero-defect $L^1$-sturdiness makes every branch total equal to the mean total, giving tight bounded surprise
-- statement:
--   A chunk system is a finite probability space equipped with a filtration `hist`, a finite list of chunks `chunk ω i`, and chunk sizes `size ω i`. Write
--
--   $$P(\omega) \quad\text{for the outcome weight}, \qquad T(\omega) = \sum_i \mathrm{size}(\omega,i) \quad\text{for the total size of a branch},$$
--
--   and let
--
--   $$F_h(\omega) = \mathbb{E}\big[\, \textstyle\sum_{j \ge h} \mathrm{size}(\omega,j) \,\big|\, \mathrm{hist}\,h\,\big] = \mathbb{E}[T \mid \mathrm{hist}\,h] - \textstyle\sum_{j < h} \mathrm{size}(\omega,j)$$
--
--   be the **conditional expected remaining size** at time $h$; the second equality holds because the sizes of the chunks before index $h$ are already known at time $h$, so they are constant on each time-$h$ atom and drop out of the conditional expectation. Write $S_{[a,b)}(\omega) = \sum_{a \le j < b} \mathrm{size}(\omega,j)$ for the **window size**.
--
--   The hypothesis $L^1$-**sturdiness with zero defect** says that the expected positive drawdown of the Doob martingale $\mathbb{E}[T \mid \mathrm{hist}\,h]$ is zero at every depth up to $m$:
--
--   $$\sum_{\omega} P(\omega)\,\max\big( \mathbb{E}[T] - \mathbb{E}[T \mid \mathrm{hist}\,h](\omega),\,0\big) = 0 \qquad (h \le m).$$
--
--   The theorem states that this forces
--
--   $$S_{[a,b)}(\omega) \le F_a(\omega) - F_b(\omega) + c_{\max}$$
--
--   for every window $a \le b$, every depth, and every branch ω.
--
--   The content is that the displayed inequality in fact holds **with no slack at all**, at $c_{\max} = 0$, for every window: one always has $S_{[a,b)}(\omega) = F_a(\omega) - F_b(\omega)$ exactly.
--
--   The reason is the depth-$m$ case, which is the step that is easy to miss. At depth $m$ the future is empty -- no index of the chunk list is $\ge m$ -- so $F_m(\omega) = 0$ and the Doob martingale there is just $\mathbb{E}[T \mid \mathrm{hist}\,m] = T(\omega)$, the branch total itself. Zero-defect sturdiness at depth $m$ forces the martingale to sit at its mean at *every* atom, and its mean is $\mathbb{E}[T]$, so
--
--   $$T(\omega) = \mathbb{E}[T] \qquad\text{for every branch } \omega.$$
--
--   Every branch therefore carries the same total. Telescoping the two displayed formulas for $F$ then leaves $\mathbb{E}[T] - T(\omega) = 0$ on both sides, and the window identity follows by subtracting:
--
--   $$F_a(\omega) - F_b(\omega) = \textstyle\sum_{j < b} \mathrm{size}(\omega,j) - \textstyle\sum_{j < a} \mathrm{size}(\omega,j) = \textstyle\sum_{a \le j < b} \mathrm{size}(\omega,j).$$
--
--   This is used to make a branchwise regrouping argument legitimate: the realised mass of any window of chunks is then *exactly* the drop of the conditional expected remaining size across that window, on every branch, with no slack to absorb. It pairs with the companion statement `sturdyL1_zero_slow_decrementC`, which shows the same hypothesis makes $F$ slowly decreasing with parameter $c_{\max}$; together they give the tame output that the regrouping step of the induction for the randomized lower bound consumes.
--
--   **Formalization Note** `SturdyL1` and `BoundedSurpriseC` are predicates of the structure `ChunkSystemB`, both stated over `condExp`/`condFuture`. The theorem uses no geometric or cost axiom of the structure and holds for any metric space and any pair of points; the parameter $c_{\max}$ appears in the conclusion only so that the result matches the shape of the regrouping hypothesis.
-- source:
--   Babenko--Bienstock--Coulhon--Regev, 'The randomized $k$-server conjecture is false: $\Omega(\log^2 k)$ lower bound' (2023), Lemma 15 regrouping step; internal reduction tracked in missions/K-Server Conjecture/artefacts/KSERVER_STURDY_SLOWDECREMENT_BRIDGE_20261002.md

import Mathlib
import Definitions.Def_KServer_sturdy
import Definitions.Def_KServer_chunk_slow_decrement_cond

namespace KServer

theorem sturdyL1_zero_bounded_surpriseC {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price : ℝ} {mLo : ℕ} (m : ℕ)
    (C : ChunkSystemB X s t cLo cHi total price mLo) (hcHi : 0 ≤ cHi)
    (hst : C.SturdyL1 m 0) :
    C.BoundedSurpriseC cHi := by sorry

end KServer
