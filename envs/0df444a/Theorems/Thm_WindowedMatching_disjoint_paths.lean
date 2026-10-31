-- Prove2me | Theorems.Thm_WindowedMatching_disjoint_paths
-- name    : WindowedMatching.disjoint_paths
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:38.098085+00:00
-- url     : https://prove2.me/theorems/f4981a44-19f6-45fa-9cc3-c19f1f540cc2
-- title:
--   The 2-matching is a collection of disjoint paths
-- statement:
--   Throughout, $d\ge1$ is the deadline, $v_{ij}\ge0$ are the weights, and the run is Postponed Greedy (Algorithm 3) on the online graph $G_{d,\sigma}$ with $\sigma(i)=i$, for an arbitrary tie-breaking rule in step 1(d). Write $p^f$, $m^f$ for the prices and matches at the end of the run, and $q(b_k)$ for the margin of the buyer $b_k$ in step 1(d).
--
--   For every outcome of the coins and all vertices $k,k',l$:
--
--   1. if $m^f(s_k)=b_l$, then $k<l$ and $(k,l)$ is an edge of $G_{d,\sigma}$;
--   2. if $m^f(s_k)=b_l$ and $m^f(s_{k'})=b_l$, then $k=k'$.
--
--   So each vertex has at most one final buyer and at most one final seller, and $k<l$ excludes cycles. The final matches thus form vertex-disjoint paths.
--
--   Differences from the source:
--   - encoding: "it is just a collection of disjoint paths" → $k<l$, adjacency, and injectivity of $m^f$ on matched sellers; reason: out-degree at most one holds because $m$ is a function, and $k<l$ excludes cycles; together these are the claim
--   - encoding: vertices $1,\dots,n$ with $\sigma(i)=i$ → `Fin n`, 0-based; vertex $k$ arrives in period $k$ and is critical in period $k+d$; reason: a shift of the index, same instances
--   - encoding: weights $v_{ij}$ on undirected pairs → `v : Sym2 (Fin n) → ℝ`; reason: symmetry by construction; the diagonal is never read
--   - encoding: a fair coin flipped when an undetermined vertex is processed in step 2(c) → one coin per vertex, `ω : Fin n → Bool`, uniform, read only in step 2(c); reason: unread coins change nothing, so the distribution is the same
--   - reading: "Process events at time $t$", with no order within a period → the arrival is processed before the criticality; reason: the edge $(i,i+d)$ exists and the proof bids on it; critical-first makes the theorem false ($n=2$, $d=1$, $v=1$ gives $\mathrm{PG}=0$, $\mathrm{OFF}=1$)
--   - reading: no stated end of the run → the run lasts $n+d$ periods; reason: every vertex must become critical; stopping at $n$ collects nothing on $n=2$, $d=2$
--   - reading: $\operatorname{argmax}$ with no tie-breaking rule → every rule `tie` choosing a maximizer as a function of the arriving vertex, the seller set and the sellers' margins, which sees no coin and no other part of the history; reason: the proof uses no property of the rule, and $p^f$ must not depend on the coins; a deterministic argmax over the margins is such a rule; one fixed rule would be weaker
--   - reading: the input is the online graph $G_{d,\sigma}$ → margins read `onlineWeight`, which is $0$ off the edges of $G_{d,\sigma}$; reason: p.6: "seller $s_k$ does not have any edges" on arrival; a seller past its deadline has no edge to a later buyer
-- source:
--   Ashlagi, Burq, Dutta, Jaillet, Saberi & Sholley, Maximum Weight Online Matching with Deadlines, arXiv:1808.03526v1, proof context, p.6, "it is just a collection of disjoint paths"

import Definitions.Def_WindowedMatching_PostponedGreedy

namespace WindowedMatching

/-- The 2-matching is a collection of disjoint paths (arXiv:1808.03526v1, §3.2, p.6, "this 2-matching
does not have any cycles; it is just a collection of disjoint paths"). If `m^f(s_k) = b_l` then
`k < l` and `(k, l)` is an edge of the online graph, and each buyer has at most one final seller.

**Formalization Note.** `m` is not cleared at criticality, and no buyer bids on `s_k` after `k`'s
criticality, so `m^f(s_k)` is the match of step 2(b). Out-degree at most one holds because `m` is a
function, in-degree at most one is the second clause, and `k < l` excludes cycles. -/
theorem disjoint_paths {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) (ω : Fin n → Bool) :
    (∀ k l, (finalState d v tie ω).m k = some l → k < l ∧ (windowGraph n d).Adj k l) ∧
    (∀ k k' l, (finalState d v tie ω).m k = some l → (finalState d v tie ω).m k' = some l →
      k = k') := by sorry

end WindowedMatching
