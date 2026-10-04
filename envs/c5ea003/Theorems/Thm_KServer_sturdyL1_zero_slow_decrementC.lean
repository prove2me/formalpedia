-- Prove2me | Theorems.Thm_KServer_sturdyL1_zero_slow_decrementC
-- name    : KServer.sturdyL1_zero_slow_decrementC
-- status  : Open
-- author  : @WillR
-- created : 2026-10-02T16:27:26.689732+00:00
-- url     : https://prove2.me/theorems/b147ce57-6a45-42e1-a80b-f789aa87ad51
-- title:
--   $L^1$-sturdiness with zero defect forces slow decrease of the conditional remaining size
-- statement:
--   A chunk system is a finite probability space equipped with a filtration `hist`, a finite list of chunks `chunk ω i`, and chunk sizes `size ω i`. Write
--
--   $$P(ω) \quad\text{for the outcome weight}, \qquad T(ω) = \sum_i \mathrm{size}(ω,i) \quad\text{for the total size of a branch},$$
--
--   and let
--
--   $$F_h(ω) = \mathbb{E}\big[\, \textstyle\sum_{j \u2265 h} \mathrm{size}(ω,j) \;\big|\; \mathrm{hist}\,h\,\big] = \mathbb{E}[T \mid \mathrm{hist}\,h] - \textstyle\sum_{j < h} \mathrm{size}(ω,j)$$
--
--   be the **conditional expected remaining size** at time $h$. The identity on the right holds because the sizes of the chunks before index $h$ are already known at time $h$: measurability of the size function with respect to the filtration makes $\sum_{j<h} \mathrm{size}(ω,j)$ constant on each time-$h$ atom, so it drops out of the conditional expectation.
--
--   The hypothesis $L^1$-**sturdiness with zero defect** says that the expected positive drawdown of the Doob martingale $\mathbb{E}[T\mid\mathrm{hist}\,h]$ is zero at every depth up to $m$:
--
--   $$\sum_{ω} P(ω)\,\max\big( \mathbb{E}[T] - \mathbb{E}[T\mid\mathrm{hist}\,h](ω),\,0\big) = 0 \qquad (h \le m).$$
--
--   The theorem states that this forces
--
--   $$F_h(ω) - c_{\max} \le F_{h+1}(ω) \qquad\text{for every } h ≥ 0 \text{ and every branch } ω,$$
--
--   that is, **the conditional expected remaining size never drops, in any
--   individual branch, by more than $c_{\max}$.** The conclusion is stated for
--   every $c_{\max} \ge 0$ and does not mention the lower size bound $c_{\min}$.
--
--   The reason is that zero-defect sturdiness is a *pointwise* statement in
--   disguise. Each summand of the hypothesis is nonnegative, so a vanishing sum
--   forces every atom of the Doob martingale at depth $h \le m$ to sit at or above
--   its mean; total expectation says their $P$-weighted average is exactly the
--   mean; and since every weight is strictly positive, each one must coincide with
--   the mean. So $\mathbb{E}[T\mid\mathrm{hist}\,h]$ is *constant* for $h \le m$, and
--   the drop of $F$ between consecutive depths collapses to the difference of the
--   realised chunk sizes
--
--   $$F_h(ω) - F_{h+1}(ω) = \mathrm{size}(ω,h),$$
--
--   which is bounded by $c_{\max}$ by hypothesis on the chunk sizes. Below depth
--   $m$ nothing else can move $F$. Past depth $m$ the displayed inequality is
--   vacuous because $c_{\max} \ge 0$.
--
--   This is the quantitative bridge between the sturdiness package and the
--   stepwise regularity package: it converts a statement about *expected*
--   drawdowns into a statement about *every* branch, which is what a branchwise
--   stopping-time or regrouping argument needs. It is used to discharge the
--   slow-decrement half of the regrouping step in the induction for the
--   randomized lower bound.
--
--   **Formalization Note** `SturdyL1` and `SlowDecrementC` are predicates of the
--   structure `ChunkSystemB`, both stated over `condExp`/`condFuture`; the theorem
--   uses no geometric or cost axiom of the structure and holds for any metric
--   space and any pair of points.
-- source:
--   Babenko--Bienstock--Coulhon--Regev, 'The randomized $k$-server conjecture is false: $\Omega(\log^2 k)$ lower bound' (2023), Lemma 15 regrouping step; internal reduction tracked in missions/K-Server Conjecture/artefacts/KSERVER_STURDY_SLOWDECREMENT_BRIDGE_20261002.md

import Mathlib
import Definitions.Def_KServer_sturdy
import Definitions.Def_KServer_chunk_slow_decrement_cond

namespace KServer

theorem sturdyL1_zero_slow_decrementC {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price : ℝ} {mLo : ℕ} (m : ℕ)
    (C : ChunkSystemB X s t cLo cHi total price mLo) (hcHi : 0 ≤ cHi)
    (hst : C.SturdyL1 m 0) :
    C.SlowDecrementC cHi := by sorry

end KServer
