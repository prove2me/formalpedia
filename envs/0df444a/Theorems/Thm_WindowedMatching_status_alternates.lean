-- Prove2me | Theorems.Thm_WindowedMatching_status_alternates
-- name    : WindowedMatching.status_alternates
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:48.32178+00:00
-- url     : https://prove2.me/theorems/54ec2d42-76b6-4edd-bc9d-f76db10a62d4
-- title:
--   Statuses alternate along a path of the 2-matching
-- statement:
--   Throughout, $d\ge1$ is the deadline, $v_{ij}\ge0$ are the weights, and the run is Postponed Greedy (Algorithm 3) on the online graph $G_{d,\sigma}$ with $\sigma(i)=i$, for an arbitrary tie-breaking rule in step 1(d). Write $p^f$, $m^f$ for the prices and matches at the end of the run, and $q(b_k)$ for the margin of the buyer $b_k$ in step 1(d).
--
--   For every outcome of the coins, if $m^f(s_k)=b_l$, then one of the following holds at the end of the run:
--
--   1. $k$ is a seller, $l$ is a buyer, and $(k,l)$ is finalized;
--   2. $k$ is a buyer, $l$ is a seller, and $(k,l)$ is not finalized.
--
--   This is the decomposition of each path into two disjoint matchings. It gives that the finalized pairs are vertex-disjoint.
--
--   Differences from the source:
--   - reading: "We decompose each path into two disjoint matchings and choose each matching with probability 1/2" → $k$ and $l$ have opposite final statuses, and $(k,l)$ is finalized exactly if $k$ is a seller; reason: this is the decomposition, as Algorithm 3 implements it; the probability is `seller_prob_half`
--   - encoding: vertices $1,\dots,n$ with $\sigma(i)=i$ → `Fin n`, 0-based; vertex $k$ arrives in period $k$ and is critical in period $k+d$; reason: a shift of the index, same instances
--   - encoding: weights $v_{ij}$ on undirected pairs → `v : Sym2 (Fin n) → ℝ`; reason: symmetry by construction; the diagonal is never read
--   - encoding: a fair coin flipped when an undetermined vertex is processed in step 2(c) → one coin per vertex, `ω : Fin n → Bool`, uniform, read only in step 2(c); reason: unread coins change nothing, so the distribution is the same
--   - reading: "Process events at time $t$", with no order within a period → the arrival is processed before the criticality; reason: the edge $(i,i+d)$ exists and the proof bids on it; critical-first makes the theorem false ($n=2$, $d=1$, $v=1$ gives $\mathrm{PG}=0$, $\mathrm{OFF}=1$)
--   - reading: no stated end of the run → the run lasts $n+d$ periods; reason: every vertex must become critical; stopping at $n$ collects nothing on $n=2$, $d=2$
--   - reading: $\operatorname{argmax}$ with no tie-breaking rule → every rule `tie` choosing a maximizer as a function of the arriving vertex, the seller set and the sellers' margins, which sees no coin and no other part of the history; reason: the proof uses no property of the rule, and $p^f$ must not depend on the coins; a deterministic argmax over the margins is such a rule; one fixed rule would be weaker
--   - reading: the input is the online graph $G_{d,\sigma}$ → margins read `onlineWeight`, which is $0$ off the edges of $G_{d,\sigma}$; reason: p.6: "seller $s_k$ does not have any edges" on arrival; a seller past its deadline has no edge to a later buyer
-- source:
--   Ashlagi, Burq, Dutta, Jaillet, Saberi & Sholley, Maximum Weight Online Matching with Deadlines, arXiv:1808.03526v1, proof context, p.6, "We decompose each path into two disjoint matchings"

import Definitions.Def_WindowedMatching_PostponedGreedy

namespace WindowedMatching

/-- Statuses alternate along a path, which decomposes it into two disjoint matchings
(arXiv:1808.03526v1, §3.2, p.6, "We decompose each path into two disjoint matchings and choose each
matching with probability 1/2"). For every outcome `ω`, if `m^f(s_k) = b_l`, then at the end of the
run `k` and `l` have opposite statuses, and `(k, l)` is finalized exactly if `k` is a seller. -/
theorem status_alternates {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) (ω : Fin n → Bool) (k l : Fin n)
    (hkl : (finalState d v tie ω).m k = some l) :
    ((finalState d v tie ω).status k = .seller ∧ (finalState d v tie ω).status l = .buyer ∧
      (k, l) ∈ (finalState d v tie ω).finalized) ∨
    ((finalState d v tie ω).status k = .buyer ∧ (finalState d v tie ω).status l = .seller ∧
      (k, l) ∉ (finalState d v tie ω).finalized) := by sorry

end WindowedMatching
