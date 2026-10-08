-- Prove2me | Theorems.Thm_YoungConventions_AdaptivePlay_example_2
-- name    : YoungConventions.AdaptivePlay.example_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:03:24.972747+00:00
-- url     : https://prove2.me/theorems/6529373f-02cf-4104-853a-411c2238db1c
-- title:
--   Example 2 — with complete sampling $k = m$, perfect miscoordination persists forever
-- statement:
--   Consider the Yield / Not Yield game of Example 2 with payoffs $(0,0)$, $(1,\sqrt2)$, $(\sqrt2,1)$, $(0,0)$. Let the sample size equal the memory, $k = m \ge 1$, and let $p$ be any best-reply distribution. Suppose the initial state $h$ is **perfectly miscoordinated**: in each of its $m$ plays both players yielded or both did not yield. Then every state $h'$ that adaptive play reaches from $h$ with positive probability, after any number $n$ of periods, is again perfectly miscoordinated:
--   $$\big((P^0)^n\big)_{hh'} > 0 \;\Longrightarrow\; h'_t \text{ has both players making the same choice, for every position } t .$$
--
--   Since the strict equilibria of this game are the coordinated outcomes (Yield, Not Yield) and (Not Yield, Yield), adaptive play started at $h$ never reaches a convention. The incomplete-sampling hypothesis $k \le m/(L_\Gamma + 2)$ of Theorem 1 therefore cannot simply be dropped.
--
--   **Formalization Note** Row is player $0$, Column is player $1$, and `true` is Yield.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, Example 2, pp. 65–66 (PDF pp. 10–11)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_IsBestReplyDistribution
import Definitions.Def_YoungConventions_AdaptivePlay_adaptivePlay
import Definitions.Def_YoungConventions_AdaptivePlay_yieldGame

namespace YoungConventions.AdaptivePlay

/-- **Example 2: with complete sampling (`k = m`) adaptive play can miscoordinate forever**
(Young 1993, *The Evolution of Conventions*, Econometrica 61:57–84, §4, Example 2, pp. 65–66,
PDF pp. 10–11): "Let `k = m`, so that both players sample the same `m` plays in each period.
Consider any initial sequence of `m` plays in which the players have always miscoordinated, that
is, they both yielded or they both failed to yield in each period. […] Thus, if they begin in a
state of perfect miscoordination, then they miscoordinate forever."

In the game `yieldGame` (Yield/Not Yield with payoffs `(0,0), (1,√2), (√2,1), (0,0)`), let
`k = m ≥ 1` and let `p` be any best-reply distribution. If in every play of the initial state `h`
both players made the same choice (both yielded or both did not), then every state `h′` that
adaptive play reaches from `h` with positive probability, after any number `n` of steps, again has
the same choice for both players in every play.

**Formalization Note.** Row is player `0`, Column is player `1`, and `true` is Yield. The sample
size is `k = m`, so the only sample is the whole history. Since the strict Nash equilibria of the
game are (Yield, Not Yield) and (Not Yield, Yield), a perfectly miscoordinated state is never a
convention, so adaptive play from `h` never reaches one. -/
theorem example_2 (m : ℕ) [NeZero m]
    (p : ∀ i : Fin 2, History (fun _ : Fin 2 => Bool) m → Bool → ℝ)
    (hp : IsBestReplyDistribution (S := fun _ : Fin 2 => Bool) yieldGame m p)
    (h : History (fun _ : Fin 2 => Bool) m) (hh : ∀ t, h t 0 = h t 1)
    (n : ℕ) (h' : History (fun _ : Fin 2 => Bool) m)
    (hpos : 0 < (adaptivePlay p ^ n) h h') :
    ∀ t, h' t 0 = h' t 1 := by sorry

end YoungConventions.AdaptivePlay
