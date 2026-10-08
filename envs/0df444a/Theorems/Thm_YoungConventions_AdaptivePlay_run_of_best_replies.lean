-- Prove2me | Theorems.Thm_YoungConventions_AdaptivePlay_run_of_best_replies
-- name    : YoungConventions.AdaptivePlay.run_of_best_replies
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:03:15.427003+00:00
-- url     : https://prove2.me/theorems/b7bcdfd4-b215-4219-9ed8-2340a63d972c
-- title:
--   Proof of Theorem 1, p. 64 — a run $(s, \dots, s)$ of $k$ best replies to the last $k$ plays
-- statement:
--   Let $\Gamma$ be a finite game, $1 \le k$ and $m \ge 2k - 1$, let $p$ be a best-reply distribution with sample size $k$, and let $h \in H$. Let $\eta$ be the sample consisting of the last $k$ positions of $h$, and let $s$ be a strategy tuple in which every $s_i$ is a best reply of player $i$ to $\eta$. Define $h^{(s)}$ as the state obtained from $h$ by deleting its $k$ oldest plays and appending $s$ $k$ times:
--   $$h^{(s)}_t = \begin{cases} h_{t+k} & \text{if } t + k < m, \\ s & \text{otherwise.} \end{cases}$$
--   Then adaptive play moves from $h$ to $h^{(s)}$ in $k$ steps with positive probability:
--   $$\big((P^0)^k\big)_{h\, h^{(s)}} > 0 .$$
--
--   This is the first step of the proof of Theorem 1. The memory condition $m \ge 2k - 1$ keeps the original $k$ plays of $\eta$ in memory throughout the $k$ periods, so every player can keep sampling $\eta$.
--
--   **Formalization Note** Position $0$ is the oldest play, so the last $k$ positions are those $t$ with $t + k \ge m$. The condition $m \ge 2k - 1$ is written $2k \le m + 1$.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, proof of Theorem 1, p. 64 (PDF p. 9)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_IsBestReplyDistribution
import Definitions.Def_YoungConventions_AdaptivePlay_adaptivePlay

namespace YoungConventions.AdaptivePlay

/-- **A run of `k` identical best replies to the last `k` plays** (Young 1993, *The Evolution of
Conventions*, Econometrica 61:57–84, proof of Theorem 1, p. 64, PDF p. 9): "In period `t + 1` there
is a positive probability that each of the `n` agents samples the last `k` plays in `h`, namely,
`(s(t − k + 1), …, s(t)) = η`. […] Thus there is a positive probability of a run `(s, s, …, s)`
from periods `t + 1` to `t + k` inclusive. Note that this argument depends on the agents' memory
being at least `2k − 1`, since otherwise they could not choose the sample `η` in period `t + k`."

Let `1 ≤ k` and `m ≥ 2k − 1`, let `p` be a best-reply distribution, `h` a state, `η` the sample
consisting of the last `k` positions of `h`, and `s` a strategy tuple in which every `sᵢ` is a best
reply of `i` to `η`. Then, after `k` steps of adaptive play from `h`, the state obtained by
deleting the `k` oldest plays of `h` and appending `s` `k` times has positive probability:
$$ (P^0)^k_{h,\,h^{(s)}} > 0,\qquad h^{(s)}_t = \begin{cases} h_{t+k} & t + k < m,\\ s & \text{otherwise.}\end{cases} $$

**Formalization Note.** Position `0` is the oldest play; the last `k` positions are
`{t : m ≤ t + k}`. The hypothesis `m ≥ 2k − 1` is written `2k ≤ m + 1` in `ℕ`. -/
theorem run_of_best_replies {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : 2 * k ≤ m + 1)
    (p : ∀ i, History S m → S i → ℝ) (hp : IsBestReplyDistribution u k p)
    (h : History S m) (s : ∀ i, S i)
    (hs : ∀ i, IsSampleBestReply u h (Finset.univ.filter fun t : Fin m => m ≤ t.val + k) i (s i)) :
    0 < (adaptivePlay p ^ k) h
      (fun t => if ht : t.val + k < m then h ⟨t.val + k, ht⟩ else s) := by sorry

end YoungConventions.AdaptivePlay
