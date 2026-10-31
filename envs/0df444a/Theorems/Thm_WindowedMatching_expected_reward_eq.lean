-- Prove2me | Theorems.Thm_WindowedMatching_expected_reward_eq
-- name    : WindowedMatching.expected_reward_eq
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:48.257884+00:00
-- url     : https://prove2.me/theorems/96b5abff-17af-4644-839b-5579e05e1d41
-- title:
--   $\mathrm{PG}=\frac12\sum_k p^f(s_k)$
-- statement:
--   Throughout, $d\ge1$ is the deadline, $v_{ij}\ge0$ are the weights, and the run is Postponed Greedy (Algorithm 3) on the online graph $G_{d,\sigma}$ with $\sigma(i)=i$, for an arbitrary tie-breaking rule in step 1(d). Write $p^f$, $m^f$ for the prices and matches at the end of the run, and $q(b_k)$ for the margin of the buyer $b_k$ in step 1(d).
--
--   The expected reward of Postponed Greedy is half the sum of the final prices:
--   $$\mathrm{PG}=\mathbb E\Big[\sum_{k\text{ is a seller}}p^f(s_k)\Big]=\frac12\sum_{k\in[1,T]}p^f(s_k).$$
--   Here $T=n$. This converts the reward of the algorithm into a quantity of the virtual run, which does not depend on the coins.
--
--   Differences from the source:
--   - encoding: $T$ and the fixed numbers $p^f(s_k)$ → $T=n$, and $p^f$ is read from an arbitrary outcome $\omega_0$; reason: $p^f$ does not depend on the coins (`virtual_run_coin_free`)
--   - encoding: the middle term $\mathbb E[\sum_{k\text{ is a seller}}p^f(s_k)]$ → omitted; only the two ends of the chain are stated; reason: the left end is the expected sum of $v_{k,l}$ over finalized pairs, which is $\mathrm{PG}$ by definition, and the middle term is that sum rewritten
--   - encoding: vertices $1,\dots,n$ with $\sigma(i)=i$ → `Fin n`, 0-based; vertex $k$ arrives in period $k$ and is critical in period $k+d$; reason: a shift of the index, same instances
--   - encoding: weights $v_{ij}$ on undirected pairs → `v : Sym2 (Fin n) → ℝ`; reason: symmetry by construction; the diagonal is never read
--   - encoding: a fair coin flipped when an undetermined vertex is processed in step 2(c) → one coin per vertex, `ω : Fin n → Bool`, uniform, read only in step 2(c); reason: unread coins change nothing, so the distribution is the same
--   - reading: "Process events at time $t$", with no order within a period → the arrival is processed before the criticality; reason: the edge $(i,i+d)$ exists and the proof bids on it; critical-first makes the theorem false ($n=2$, $d=1$, $v=1$ gives $\mathrm{PG}=0$, $\mathrm{OFF}=1$)
--   - reading: no stated end of the run → the run lasts $n+d$ periods; reason: every vertex must become critical; stopping at $n$ collects nothing on $n=2$, $d=2$
--   - reading: $\operatorname{argmax}$ with no tie-breaking rule → every rule `tie` choosing a maximizer as a function of the arriving vertex, the seller set and the sellers' margins, which sees no coin and no other part of the history; reason: the proof uses no property of the rule, and $p^f$ must not depend on the coins; a deterministic argmax over the margins is such a rule; one fixed rule would be weaker
--   - reading: the input is the online graph $G_{d,\sigma}$ → margins read `onlineWeight`, which is $0$ off the edges of $G_{d,\sigma}$; reason: p.6: "seller $s_k$ does not have any edges" on arrival; a seller past its deadline has no edge to a later buyer
-- source:
--   Ashlagi, Burq, Dutta, Jaillet, Saberi & Sholley, Maximum Weight Online Matching with Deadlines, arXiv:1808.03526v1, Theorem 3.3, proof, display, p.6

import Definitions.Def_WindowedMatching_PostponedGreedy

namespace WindowedMatching

/-- `PG = 𝔼[Σ_{k is a seller} p^f(s_k)] = ½ Σ_{k ∈ [1,T]} p^f(s_k)` (arXiv:1808.03526v1, §3.2,
proof of Theorem 3.3, display, p.6).

**Formalization Note.** `T` is the number of vertices `n`. The final prices are the same for all
outcomes of the coins (`virtual_run_coin_free`), so they are read from an arbitrary outcome `ω₀`. -/
theorem expected_reward_eq {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) (ω₀ : Fin n → Bool) :
    expectedReward d v tie = (1 / 2) * ∑ k, (finalState d v tie ω₀).p k := by sorry

end WindowedMatching
