-- Prove2me | Theorems.Thm_WindowedMatching_sum_price_eq_sum_margin
-- name    : WindowedMatching.sum_price_eq_sum_margin
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:37.993013+00:00
-- url     : https://prove2.me/theorems/c748398a-d67a-4cd6-a21c-b6d124989990
-- title:
--   $\sum_s p^f(s)=\sum_b q(b)$
-- statement:
--   Throughout, $d\ge1$ is the deadline, $v_{ij}\ge0$ are the weights, and the run is Postponed Greedy (Algorithm 3) on the online graph $G_{d,\sigma}$ with $\sigma(i)=i$, for an arbitrary tie-breaking rule in step 1(d). Write $p^f$, $m^f$ for the prices and matches at the end of the run, and $q(b_k)$ for the margin of the buyer $b_k$ in step 1(d).
--
--   Every increase in a virtual seller's price corresponds to a virtual buyer's margin, so
--   $$\sum_{s\in S}p^f(s)=\sum_{b\in B}q(b),$$
--   where $S=\cup_tS_t$ and $B=\cup_tB_t$.
--
--   This identity lets the dual value be written in terms of the prices alone.
--
--   Differences from the source:
--   - encoding: $S=\cup_tS_t$ and $B=\cup_tB_t$ → both sums run over `Fin n`; reason: every vertex contributes exactly one seller and one buyer
--   - encoding: vertices $1,\dots,n$ with $\sigma(i)=i$ → `Fin n`, 0-based; vertex $k$ arrives in period $k$ and is critical in period $k+d$; reason: a shift of the index, same instances
--   - encoding: weights $v_{ij}$ on undirected pairs → `v : Sym2 (Fin n) → ℝ`; reason: symmetry by construction; the diagonal is never read
--   - encoding: a fair coin flipped when an undetermined vertex is processed in step 2(c) → one coin per vertex, `ω : Fin n → Bool`, uniform, read only in step 2(c); reason: unread coins change nothing, so the distribution is the same
--   - reading: "Process events at time $t$", with no order within a period → the arrival is processed before the criticality; reason: the edge $(i,i+d)$ exists and the proof bids on it; critical-first makes the theorem false ($n=2$, $d=1$, $v=1$ gives $\mathrm{PG}=0$, $\mathrm{OFF}=1$)
--   - reading: no stated end of the run → the run lasts $n+d$ periods; reason: every vertex must become critical; stopping at $n$ collects nothing on $n=2$, $d=2$
--   - reading: $\operatorname{argmax}$ with no tie-breaking rule → every rule `tie` choosing a maximizer as a function of the arriving vertex, the seller set and the sellers' margins, which sees no coin and no other part of the history; reason: the proof uses no property of the rule, and $p^f$ must not depend on the coins; a deterministic argmax over the margins is such a rule; one fixed rule would be weaker
--   - reading: the input is the online graph $G_{d,\sigma}$ → margins read `onlineWeight`, which is $0$ off the edges of $G_{d,\sigma}$; reason: p.6: "seller $s_k$ does not have any edges" on arrival; a seller past its deadline has no edge to a later buyer
-- source:
--   Ashlagi, Burq, Dutta, Jaillet, Saberi & Sholley, Maximum Weight Online Matching with Deadlines, arXiv:1808.03526v1, Theorem 3.3, proof, p.7

import Definitions.Def_WindowedMatching_PostponedGreedy

namespace WindowedMatching

/-- `Σ_{s ∈ S} p^f(s) = Σ_{b ∈ B} q(b)`: every increase in a virtual seller's price corresponds to
a virtual buyer's margin (arXiv:1808.03526v1, §3.2, proof of Theorem 3.3, p.7).

**Formalization Note.** `S = ∪_t S_t` and `B = ∪_t B_t` are all `n` copies, so both sums run over
`Fin n`. -/
theorem sum_price_eq_sum_margin {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) (ω : Fin n → Bool) :
    ∑ k, (finalState d v tie ω).p k = ∑ k, (finalState d v tie ω).q k := by sorry

end WindowedMatching
