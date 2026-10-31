-- Prove2me | Theorems.Thm_WindowedMatching_margin_ge
-- name    : WindowedMatching.margin_ge
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:02.172407+00:00
-- url     : https://prove2.me/theorems/fc11fec6-203d-4a21-9a4c-e4fd2d95539a
-- title:
--   $q(b_j)\ge v_{ij}-p(s_i)$ when $j$ arrives
-- statement:
--   Throughout, $d\ge1$ is the deadline, $v_{ij}\ge0$ are the weights, and the run is Postponed Greedy (Algorithm 3) on the online graph $G_{d,\sigma}$ with $\sigma(i)=i$, for an arbitrary tie-breaking rule in step 1(d). Write $p^f$, $m^f$ for the prices and matches at the end of the run, and $q(b_k)$ for the margin of the buyer $b_k$ in step 1(d).
--
--   Let $i<j$ be vertices with $j-i\le d$. When $j$ arrives,
--   $$q(b_j)\ge v_{ij}-p(s_i),$$
--   where $p(s_i)$ is the price at the start of period $j$.
--
--   The seller $s_i$ is still present when $j$ arrives, because the criticality of $i$ does not come before the arrival of $j$. This is the first half of dual feasibility.
--
--   Differences from the source:
--   - encoding: "When $j$ arrives" → $p(s_i)$ in the state after $j$ periods and $q(b_j)$ in the state after $j+1$ periods; reason: steps 1(a)–(c) do not change $p(s_i)$ for $i\ne j$, and $q(b_j)$ is written in period $j$
--   - encoding: $j-i\le d$ → $j\le i+d$; reason: the same condition for $i<j$, without truncated subtraction
--   - encoding: vertices $1,\dots,n$ with $\sigma(i)=i$ → `Fin n`, 0-based; vertex $k$ arrives in period $k$ and is critical in period $k+d$; reason: a shift of the index, same instances
--   - encoding: weights $v_{ij}$ on undirected pairs → `v : Sym2 (Fin n) → ℝ`; reason: symmetry by construction; the diagonal is never read
--   - encoding: a fair coin flipped when an undetermined vertex is processed in step 2(c) → one coin per vertex, `ω : Fin n → Bool`, uniform, read only in step 2(c); reason: unread coins change nothing, so the distribution is the same
--   - reading: "Process events at time $t$", with no order within a period → the arrival is processed before the criticality; reason: the edge $(i,i+d)$ exists and the proof bids on it; critical-first makes the theorem false ($n=2$, $d=1$, $v=1$ gives $\mathrm{PG}=0$, $\mathrm{OFF}=1$)
--   - reading: no stated end of the run → the run lasts $n+d$ periods; reason: every vertex must become critical; stopping at $n$ collects nothing on $n=2$, $d=2$
--   - reading: $\operatorname{argmax}$ with no tie-breaking rule → every rule `tie` choosing a maximizer as a function of the arriving vertex, the seller set and the sellers' margins, which sees no coin and no other part of the history; reason: the proof uses no property of the rule, and $p^f$ must not depend on the coins; a deterministic argmax over the margins is such a rule; one fixed rule would be weaker
--   - reading: the input is the online graph $G_{d,\sigma}$ → margins read `onlineWeight`, which is $0$ off the edges of $G_{d,\sigma}$; reason: p.6: "seller $s_k$ does not have any edges" on arrival; a seller past its deadline has no edge to a later buyer
-- source:
--   Ashlagi, Burq, Dutta, Jaillet, Saberi & Sholley, Maximum Weight Online Matching with Deadlines, arXiv:1808.03526v1, Theorem 3.3, proof, p.7, "When j arrives, we have q(bj) ≥ vij − p(si)"

import Definitions.Def_WindowedMatching_PostponedGreedy

namespace WindowedMatching

/-- For `j > i` with `j − i ≤ d`, when `j` arrives, `q(b_j) ≥ v_ij − p(s_i)` (arXiv:1808.03526v1,
§3.2, proof of Theorem 3.3, p.7).

**Formalization Note.** `p(s_i)` is read in the state after `j` periods, which is the state in which
period `j` starts. Step 1(a)–(c) changes only `p(s_j)`, so this is the price in step 1(d) for `j`.
`q(b_j)` is written in period `j`, hence is read in the state after `j + 1` periods. `j ≤ i + d` is
`j − i ≤ d` for `i < j`, without truncated subtraction. -/
theorem margin_ge {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) (ω : Fin n → Bool) (i j : Fin n) (hij : i < j)
    (hj : (j : ℕ) ≤ i + d) :
    v s(i, j) - (stateAfter d v tie ω j).p i ≤ (stateAfter d v tie ω (j + 1)).q j := by sorry

end WindowedMatching
