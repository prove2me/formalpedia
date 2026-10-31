-- Prove2me | Theorems.Thm_WindowedMatching_theorem_3_3
-- name    : WindowedMatching.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:43.842009+00:00
-- url     : https://prove2.me/theorems/dee01d38-b7f5-4ec2-aa2a-d9f78fc79a84
-- title:
--   Theorem 3.3 — Postponed Greedy is $1/4$-competitive for arbitrary online graphs
-- statement:
--   The postponed greedy (PG) algorithm is $\frac14$-competitive for arbitrary online graphs.
--
--   Let $n$ be the number of vertices, let $d\ge1$ be the deadline, let $v_{ij}\ge0$ be arbitrary weights with $\sigma(i)=i$, and fix any tie-breaking rule for the $\operatorname{argmax}$ in step 1(d) of Algorithm 3. Then:
--
--   1. for every outcome of the coins, every finalized pair is an edge of the online graph $G_{d,\sigma}$;
--   2. for every outcome of the coins, the finalized pairs are vertex-disjoint;
--   3. the expected reward over $n$ independent fair coins is at least a quarter of the maximum weight of a matching of $G_{d,\sigma}$:
--   $$\mathrm{PG}\ge\frac14\,\mathrm{OFF};$$
--   4. the run is online: if two instances have the same weights on all pairs of vertices of index $<t$, and two outcomes of the coins agree on every $k$ with $k+d<t$, then the states after $t$ periods are equal.
--
--   Clauses 1 and 2 say that the algorithm outputs a matching of $G_{d,\sigma}$. Clause 3 is the competitive ratio. Clause 4 is the content of "online": decisions read only weights already observed and coins of vertices already critical.
--
--   Differences from the source:
--   - reading: "1/4-competitive" and "online algorithm" (p.4) → four clauses: the output is a matching of $G_{d,\sigma}$ (edges, disjointness), the expected bound, and dependence of the state after $t$ periods only on weights among arrived vertices and coins of critical vertices; reason: p.4 says only that the algorithm obtains a high fraction of the benchmark in expectation; the theorem presupposes a matching and an online run, so both are stated
--   - encoding: $\mathbb E[\cdot]$ over the algorithm's coins → $\frac1{2^n}\sum_\omega$; reason: the uniform average over `Fin n → Bool`; the weights are fixed before the coins, an oblivious adversary, as in the proof
--   - encoding: "the expected maximum-weight of a matching over $G_{d,\sigma}$" → `offlineOpt`, with no expectation; reason: in the Adversarial Order setting $\sigma$ is fixed
--   - encoding: vertices $1,\dots,n$ with $\sigma(i)=i$ → `Fin n`, 0-based; vertex $k$ arrives in period $k$ and is critical in period $k+d$; reason: a shift of the index, same instances
--   - encoding: weights $v_{ij}$ on undirected pairs → `v : Sym2 (Fin n) → ℝ`; reason: symmetry by construction; the diagonal is never read
--   - encoding: a fair coin flipped when an undetermined vertex is processed in step 2(c) → one coin per vertex, `ω : Fin n → Bool`, uniform, read only in step 2(c); reason: unread coins change nothing, so the distribution is the same
--   - reading: "Process events at time $t$", with no order within a period → the arrival is processed before the criticality; reason: the edge $(i,i+d)$ exists and the proof bids on it; critical-first makes the theorem false ($n=2$, $d=1$, $v=1$ gives $\mathrm{PG}=0$, $\mathrm{OFF}=1$)
--   - reading: no stated end of the run → the run lasts $n+d$ periods; reason: every vertex must become critical; stopping at $n$ collects nothing on $n=2$, $d=2$
--   - reading: $\operatorname{argmax}$ with no tie-breaking rule → every rule `tie` choosing a maximizer as a function of the arriving vertex, the seller set and the sellers' margins, which sees no coin and no other part of the history; reason: the proof uses no property of the rule, and $p^f$ must not depend on the coins; a deterministic argmax over the margins is such a rule; one fixed rule would be weaker
--   - reading: the input is the online graph $G_{d,\sigma}$ → margins read `onlineWeight`, which is $0$ off the edges of $G_{d,\sigma}$; reason: p.6: "seller $s_k$ does not have any edges" on arrival; a seller past its deadline has no edge to a later buyer
-- source:
--   Ashlagi, Burq, Dutta, Jaillet, Saberi & Sholley, Maximum Weight Online Matching with Deadlines, arXiv:1808.03526v1, Theorem 3.3, p.6 (proof pp.6–7; Algorithm 3, p.7; model, §2, p.4)

import Definitions.Def_WindowedMatching_PostponedGreedy

namespace WindowedMatching

/-- **Theorem 3.3** (arXiv:1808.03526v1, p.6): the postponed greedy (PG) algorithm is
`1/4`-competitive for arbitrary online graphs. For every `n`, every `d ≥ 1`, all non-negative weights
and every tie-breaking rule:

1. every finalized pair is an edge of the online graph `G_{d,σ}`, for every outcome of the coins;
2. the finalized pairs are vertex-disjoint, for every outcome of the coins;
3. the expected reward is at least `¼` of the maximum weight of a matching over `G_{d,σ}`;
4. the run is online: the state after `t` periods reads only the weights between vertices that have
   arrived and the coins of vertices that have become critical.

**Formalization Note.** "Competitive" is the definition on p.4. The weights `v` are quantified before
the coins, an oblivious adversary. `T = n` and `σ(i) = i` (Adversarial Order). The arrival is
processed before the criticality in a period, and the run lasts `n + d` periods. -/
theorem theorem_3_3 {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) :
    (∀ ω, ∀ e ∈ (finalState d v tie ω).finalized, (windowGraph n d).Adj e.1 e.2) ∧
    (∀ ω, ((finalState d v tie ω).finalized.flatMap fun e => [e.1, e.2]).Nodup) ∧
    (1 / 4 : ℝ) * offlineOpt d v ≤ expectedReward d v tie ∧
    (∀ t ≤ n + d, ∀ v' : Sym2 (Fin n) → ℝ, (∀ e, 0 ≤ v' e) →
      (∀ i j : Fin n, (i : ℕ) < t → (j : ℕ) < t → v s(i, j) = v' s(i, j)) →
      ∀ ω ω' : Fin n → Bool, (∀ k : Fin n, (k : ℕ) + d < t → ω k = ω' k) →
        stateAfter d v tie ω t = stateAfter d v' tie ω' t) := by sorry

end WindowedMatching
