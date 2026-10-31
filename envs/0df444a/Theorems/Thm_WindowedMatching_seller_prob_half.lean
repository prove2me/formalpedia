-- Prove2me | Theorems.Thm_WindowedMatching_seller_prob_half
-- name    : WindowedMatching.seller_prob_half
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:51.511097+00:00
-- url     : https://prove2.me/theorems/5ac0d1f2-e8f5-451c-8082-ce39d1dbe858
-- title:
--   A matched vertex is a seller with probability exactly $1/2$
-- statement:
--   Throughout, $d\ge1$ is the deadline, $v_{ij}\ge0$ are the weights, and the run is Postponed Greedy (Algorithm 3) on the online graph $G_{d,\sigma}$ with $\sigma(i)=i$, for an arbitrary tie-breaking rule in step 1(d). Write $p^f$, $m^f$ for the prices and matches at the end of the run, and $q(b_k)$ for the margin of the buyer $b_k$ in step 1(d).
--
--   If $m^f(s_k)\neq\emptyset$, then of the $2^n$ outcomes of the coins, exactly $2^{n-1}$ make $k$ a seller. That is,
--   $$\Pr[k\text{ is a seller}]=\frac12.$$
--
--   Together with the fact that a vertex with no final match has $p^f(s_k)=0$, this gives the formula for $\mathrm{PG}$.
--
--   Differences from the source:
--   - reading: "this happens with probability exactly 1/2 for every $k$" → stated for $k$ with $m^f(s_k)\neq\emptyset$; reason: the sentence is about $k$ reaching step 2(c); a vertex with no match and no predecessor is never a seller ($n=1$ gives probability $0$), and such a vertex has $p^f(s_k)=0$
--   - encoding: $k$'s status in step 2(c)i → $k$'s status at the end of the run; reason: step 2(c) writes it and nothing writes it later
--   - encoding: $m^f$ as a fixed object → $m^f$ read from an arbitrary outcome $\omega_0$; reason: $m^f$ does not depend on the coins (`virtual_run_coin_free`)
--   - encoding: vertices $1,\dots,n$ with $\sigma(i)=i$ → `Fin n`, 0-based; vertex $k$ arrives in period $k$ and is critical in period $k+d$; reason: a shift of the index, same instances
--   - encoding: weights $v_{ij}$ on undirected pairs → `v : Sym2 (Fin n) → ℝ`; reason: symmetry by construction; the diagonal is never read
--   - encoding: a fair coin flipped when an undetermined vertex is processed in step 2(c) → one coin per vertex, `ω : Fin n → Bool`, uniform, read only in step 2(c); reason: unread coins change nothing, so the distribution is the same
--   - reading: "Process events at time $t$", with no order within a period → the arrival is processed before the criticality; reason: the edge $(i,i+d)$ exists and the proof bids on it; critical-first makes the theorem false ($n=2$, $d=1$, $v=1$ gives $\mathrm{PG}=0$, $\mathrm{OFF}=1$)
--   - reading: no stated end of the run → the run lasts $n+d$ periods; reason: every vertex must become critical; stopping at $n$ collects nothing on $n=2$, $d=2$
--   - reading: $\operatorname{argmax}$ with no tie-breaking rule → every rule `tie` choosing a maximizer as a function of the arriving vertex, the seller set and the sellers' margins, which sees no coin and no other part of the history; reason: the proof uses no property of the rule, and $p^f$ must not depend on the coins; a deterministic argmax over the margins is such a rule; one fixed rule would be weaker
--   - reading: the input is the online graph $G_{d,\sigma}$ → margins read `onlineWeight`, which is $0$ off the edges of $G_{d,\sigma}$; reason: p.6: "seller $s_k$ does not have any edges" on arrival; a seller past its deadline has no edge to a later buyer
-- source:
--   Ashlagi, Burq, Dutta, Jaillet, Saberi & Sholley, Maximum Weight Online Matching with Deadlines, arXiv:1808.03526v1, Theorem 3.3, proof, p.6, "Note that this happens with probability exactly 1/2 for every k"

import Definitions.Def_WindowedMatching_PostponedGreedy

namespace WindowedMatching

/-- A vertex with a final match is a seller with probability exactly `1/2` (arXiv:1808.03526v1,
§3.2, proof of Theorem 3.3, p.6, "Note that this happens with probability exactly 1/2 for every k"):
of the `2 ^ n` outcomes of the coins, exactly `2 ^ (n - 1)` make `k` a seller.

**Formalization Note.** The claim is read for vertices `k` that reach step 2(c), that is, with
`m^f(s_k) ≠ ∅`. For `n = 1` the only vertex has no match and is never a seller, and such a vertex has
`p^f(s_k) = 0`, so the display on p.6 is unaffected. The status at the end of the run is the status
when step 2(c) processes `k`: step 2(c) writes it and nothing writes it later. `k : Fin n` gives
`1 ≤ n`, so `n - 1` is not truncated. The final `m` is the same for all outcomes of the coins
(`virtual_run_coin_free`), so the hypothesis reads it from an arbitrary outcome `ω₀`. -/
theorem seller_prob_half {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) (k : Fin n)
    (ω₀ : Fin n → Bool) (hk : (finalState d v tie ω₀).m k ≠ none) :
    (Finset.univ.filter fun ω : Fin n → Bool =>
      (finalState d v tie ω).status k = .seller).card = 2 ^ (n - 1) := by sorry

end WindowedMatching
