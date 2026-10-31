-- Prove2me | Theorems.Thm_WindowedMatching_price_mono
-- name    : WindowedMatching.price_mono
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:44.406804+00:00
-- url     : https://prove2.me/theorems/c443304e-bfa5-4478-9da4-8d44186928f4
-- title:
--   $p(s)$ increases over time
-- statement:
--   Throughout, $d\ge1$ is the deadline, $v_{ij}\ge0$ are the weights, and the run is Postponed Greedy (Algorithm 3) on the online graph $G_{d,\sigma}$ with $\sigma(i)=i$, for an arbitrary tie-breaking rule in step 1(d). Write $p^f$, $m^f$ for the prices and matches at the end of the run, and $q(b_k)$ for the margin of the buyer $b_k$ in step 1(d).
--
--   After the arrival of a seller $s$, its price is non-decreasing in time: for periods $t_1\le t_2$ with $t_1$ after the arrival of $s$, the price of $s$ after $t_1$ periods is at most its price after $t_2$ periods. In particular, it is at most $p^f(s)$.
--
--   Together with the margin bound at the arrival of $j$, this gives dual feasibility at the final prices.
--
--   Differences from the source:
--   - encoding: "p(s) increases over time" → non-decreasing in $t$ from the state after the arrival of $s$; reason: the state before $s$ arrives has no such seller; a step may leave a price unchanged
--   - encoding: vertices $1,\dots,n$ with $\sigma(i)=i$ → `Fin n`, 0-based; vertex $k$ arrives in period $k$ and is critical in period $k+d$; reason: a shift of the index, same instances
--   - encoding: weights $v_{ij}$ on undirected pairs → `v : Sym2 (Fin n) → ℝ`; reason: symmetry by construction; the diagonal is never read
--   - encoding: a fair coin flipped when an undetermined vertex is processed in step 2(c) → one coin per vertex, `ω : Fin n → Bool`, uniform, read only in step 2(c); reason: unread coins change nothing, so the distribution is the same
--   - reading: "Process events at time $t$", with no order within a period → the arrival is processed before the criticality; reason: the edge $(i,i+d)$ exists and the proof bids on it; critical-first makes the theorem false ($n=2$, $d=1$, $v=1$ gives $\mathrm{PG}=0$, $\mathrm{OFF}=1$)
--   - reading: no stated end of the run → the run lasts $n+d$ periods; reason: every vertex must become critical; stopping at $n$ collects nothing on $n=2$, $d=2$
--   - reading: $\operatorname{argmax}$ with no tie-breaking rule → every rule `tie` choosing a maximizer as a function of the arriving vertex, the seller set and the sellers' margins, which sees no coin and no other part of the history; reason: the proof uses no property of the rule, and $p^f$ must not depend on the coins; a deterministic argmax over the margins is such a rule; one fixed rule would be weaker
--   - reading: the input is the online graph $G_{d,\sigma}$ → margins read `onlineWeight`, which is $0$ off the edges of $G_{d,\sigma}$; reason: p.6: "seller $s_k$ does not have any edges" on arrival; a seller past its deadline has no edge to a later buyer
-- source:
--   Ashlagi, Burq, Dutta, Jaillet, Saberi & Sholley, Maximum Weight Online Matching with Deadlines, arXiv:1808.03526v1, Theorem 3.3, proof, p.7, "the fact that p(s) increases over time"

import Definitions.Def_WindowedMatching_PostponedGreedy

namespace WindowedMatching

/-- `p(s)` increases over time (arXiv:1808.03526v1, §3.2, proof of Theorem 3.3, p.7, "the fact that
p(s) increases over time"): after the arrival of `s`, the price of `s` is non-decreasing in `t`. In
particular it is at most `p^f(s)`, taking `t₂ = n + d`.

**Formalization Note.** `s < t₁` says that the state after `t₁` periods contains period `s`, the
arrival of `s`. -/
theorem price_mono {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) (ω : Fin n → Bool) (s : Fin n) (t₁ t₂ : ℕ) (hs : (s : ℕ) < t₁)
    (ht : t₁ ≤ t₂) :
    (stateAfter d v tie ω t₁).p s ≤ (stateAfter d v tie ω t₂).p s := by sorry

end WindowedMatching
