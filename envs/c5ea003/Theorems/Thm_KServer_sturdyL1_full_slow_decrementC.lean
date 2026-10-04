-- Prove2me | Theorems.Thm_KServer_sturdyL1_full_slow_decrementC
-- name    : KServer.sturdyL1_full_slow_decrementC
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-02T18:07:32.100603+00:00
-- url     : https://prove2.me/theorems/fcbebddc-3846-419d-9b03-b75172ce392e
-- title:
--   $L^1$-sturdiness with zero defect at the full chunk depth forces slow decrease of the conditional remaining size
-- statement:
--   A chunk system is a finite probability space equipped with a filtration `hist`, a finite list of chunks `chunk ω i`, and chunk sizes `size ω i`. Write
--
--   $$P(\omega) \quad\text{for the outcome weight}, \qquad T(\omega) = \sum_i \mathrm{size}(\omega,i) \quad\text{for the total size of a branch},$$
--
--   and let
--
--   $$F_h(\omega) = \mathbb{E}\big[\, \textstyle\sum_{j \ge h} \mathrm{size}(\omega,j) \;\big|\; \mathrm{hist}\,h\,\big] = \mathbb{E}[T \mid \mathrm{hist}\,h] - \textstyle\sum_{j < h} \mathrm{size}(\omega,j)$$
--
--   be the **conditional expected remaining size** at time $h$. The identity on the right holds because the sizes of the chunks before index $h$ are already known at time $h$: measurability of the size function with respect to the filtration makes $\sum_{j<h} \mathrm{size}(\omega,j)$ constant on each time-$h$ atom, so it drops out of the conditional expectation.
--
--   The hypothesis is $L^1$-**sturdiness with zero defect at the full depth** of the system, i.e. $m$ is the number of chunks and
--
--   $$\sum_{\omega} P(\omega)\,\max\big( \mathbb{E}[T] - \mathbb{E}[T\mid\mathrm{hist}\,h](\omega),\,0\big) = 0 \qquad (h \le m).$$
--
--   Because every summand is nonnegative and $P(\omega) > 0$, this forces the Doob martingale $\mathbb{E}[T\mid\mathrm{hist}\,h](\omega)$ of the total to sit exactly at its mean $\mathbb{E}[T]$ at **every** depth $h \le m$, for **every** branch $\omega$. (The step from an average statement to a pointwise one is exactly where the drawdown sum being zero, rather than merely small, is used.)
--
--   The theorem states that this forces
--
--   $$F_h(\omega) - c_{\max} \le F_{h+1}(\omega) \qquad\text{for every } h \ge 0 \text{ and every branch } \omega,$$
--
--   that is, **the conditional expected remaining size never drops, in any individual branch, by more than $c_{\max}$**, the largest permitted chunk size. Since $F_h(\omega) = \mathbb{E}[T] - \sum_{j<h}\mathrm{size}(\omega,j)$ on this range, the drop between consecutive depths is exactly the single realised chunk size $\mathrm{size}(\omega,h)$, which lies in $[c_{\min}, c_{\max}]$ by hypothesis; beyond depth $m$ there are no chunks left and the inequality is vacuous. The conclusion is stated for every $c_{\max} \ge 0$ and does not mention the lower size bound $c_{\min}$.
--
--   **The depth in the hypothesis is the number of chunks.** Sturdiness at a smaller depth is not enough and the corresponding statement is false: it only controls the Doob martingale for $h$ at or below that smaller depth, while the conclusion quantifies over every $h$, leaving the indices strictly between the sturdiness depth and the last chunk unconstrained.

import Mathlib
import Definitions.Def_KServer_sturdy
import Definitions.Def_KServer_chunk_slow_decrement_cond

namespace KServer

theorem sturdyL1_full_slow_decrementC {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price : ℝ} {mLo : ℕ} (hcHi : 0 ≤ cHi)
    (C : ChunkSystemB X s t cLo cHi total price mLo)
    (hst : C.SturdyL1 C.m 0) :
    C.SlowDecrementC cHi := by sorry

end KServer
