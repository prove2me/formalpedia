-- Prove2me | Theorems.Thm_WindowedMatching_virtual_run_coin_free
-- name    : WindowedMatching.virtual_run_coin_free
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:26.827+00:00
-- url     : https://prove2.me/theorems/205516f3-eb12-4490-b520-b60f2acab3c7
-- title:
--   The virtual greedy run reads no coin
-- statement:
--   Throughout, $d\ge1$ is the deadline, $v_{ij}\ge0$ are the weights, and the run is Postponed Greedy (Algorithm 3) on the online graph $G_{d,\sigma}$ with $\sigma(i)=i$, for an arbitrary tie-breaking rule in step 1(d). Write $p^f$, $m^f$ for the prices and matches at the end of the run, and $q(b_k)$ for the margin of the buyer $b_k$ in step 1(d).
--
--   For all outcomes $\omega,\omega'$ of the coins and every period $t$, the sets $S$, $B$, the prices $p$, the matches $m$ and the margins $q$ after $t$ periods are the same under $\omega$ and $\omega'$.
--
--   This is what makes the final prices $p^f(s_k)$ numbers, which the display on p.6 pulls out of the expectation.
--
--   Differences from the source:
--   - reading: "Then we run the greedy algorithm with the virtual graph as input" → $S,B,p,m,q$ after every period are equal for all outcomes of the coins; reason: this is the property the proof uses; Algorithm 3 is one state machine, whose statuses do depend on the coins
--   - encoding: vertices $1,\dots,n$ with $\sigma(i)=i$ → `Fin n`, 0-based; vertex $k$ arrives in period $k$ and is critical in period $k+d$; reason: a shift of the index, same instances
--   - encoding: weights $v_{ij}$ on undirected pairs → `v : Sym2 (Fin n) → ℝ`; reason: symmetry by construction; the diagonal is never read
--   - encoding: a fair coin flipped when an undetermined vertex is processed in step 2(c) → one coin per vertex, `ω : Fin n → Bool`, uniform, read only in step 2(c); reason: unread coins change nothing, so the distribution is the same
--   - reading: "Process events at time $t$", with no order within a period → the arrival is processed before the criticality; reason: the edge $(i,i+d)$ exists and the proof bids on it; critical-first makes the theorem false ($n=2$, $d=1$, $v=1$ gives $\mathrm{PG}=0$, $\mathrm{OFF}=1$)
--   - reading: no stated end of the run → the run lasts $n+d$ periods; reason: every vertex must become critical; stopping at $n$ collects nothing on $n=2$, $d=2$
--   - reading: $\operatorname{argmax}$ with no tie-breaking rule → every rule `tie` choosing a maximizer as a function of the arriving vertex, the seller set and the sellers' margins, which sees no coin and no other part of the history; reason: the proof uses no property of the rule, and $p^f$ must not depend on the coins; a deterministic argmax over the margins is such a rule; one fixed rule would be weaker
--   - reading: the input is the online graph $G_{d,\sigma}$ → margins read `onlineWeight`, which is $0$ off the edges of $G_{d,\sigma}$; reason: p.6: "seller $s_k$ does not have any edges" on arrival; a seller past its deadline has no edge to a later buyer
-- source:
--   Ashlagi, Burq, Dutta, Jaillet, Saberi & Sholley, Maximum Weight Online Matching with Deadlines, arXiv:1808.03526v1, Virtual run, p.6, "Then we run the greedy algorithm with the virtual graph as input"

import Definitions.Def_WindowedMatching_PostponedGreedy

namespace WindowedMatching

/-- The virtual greedy run reads no coin: `S`, `B`, `p`, `m` and `q` after every period are the same
for all outcomes of the coins (arXiv:1808.03526v1, §3.2, p.6, "Then we run the greedy algorithm with
the virtual graph as input"). The display on p.6 uses this when it treats `p^f(s_k)` as a number.

**Formalization Note.** The statement is a claim about Algorithm 3 as one state machine, in which
`status` and `finalized` do depend on the coins. -/
theorem virtual_run_coin_free {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) (ω ω' : Fin n → Bool) (t : ℕ) :
    (stateAfter d v tie ω t).S = (stateAfter d v tie ω' t).S ∧
    (stateAfter d v tie ω t).B = (stateAfter d v tie ω' t).B ∧
    (stateAfter d v tie ω t).p = (stateAfter d v tie ω' t).p ∧
    (stateAfter d v tie ω t).m = (stateAfter d v tie ω' t).m ∧
    (stateAfter d v tie ω t).q = (stateAfter d v tie ω' t).q := by sorry

end WindowedMatching
