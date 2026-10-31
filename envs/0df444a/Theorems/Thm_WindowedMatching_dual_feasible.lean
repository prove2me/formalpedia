-- Prove2me | Theorems.Thm_WindowedMatching_dual_feasible
-- name    : WindowedMatching.dual_feasible
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:41.037164+00:00
-- url     : https://prove2.me/theorems/689c223c-51d0-4981-804e-08b742f86135
-- title:
--   $\{p^f(s_k)+q(b_k)\}_k$ is feasible for (Offline Dual)
-- statement:
--   Throughout, $d\ge1$ is the deadline, $v_{ij}\ge0$ are the weights, and the run is Postponed Greedy (Algorithm 3) on the online graph $G_{d,\sigma}$ with $\sigma(i)=i$, for an arbitrary tie-breaking rule in step 1(d). Write $p^f$, $m^f$ for the prices and matches at the end of the run, and $q(b_k)$ for the margin of the buyer $b_k$ in step 1(d).
--
--   Let $\lambda_k=p^f(s_k)+q(b_k)$. Then $\lambda_k\ge0$ for every $k$, and
--   $$v_{kl}\le\lambda_k+\lambda_l$$
--   for every edge $(k,l)$ of $G_{d,\sigma}$. So $\lambda$ is a feasible solution of (Offline Dual), the dual of the offline matching program.
--
--   Differences from the source:
--   - encoding: the constraint $v_{kl}\le\lambda_k+\lambda_l$ for all $(k,l)$ with $|k-l|\le d$ → the constraint on edges of the `SimpleGraph` `windowGraph n d`, so for $k\ne l$; reason: the program is the dual of a matching problem, whose edges are between two vertices
--   - encoding: vertices $1,\dots,n$ with $\sigma(i)=i$ → `Fin n`, 0-based; vertex $k$ arrives in period $k$ and is critical in period $k+d$; reason: a shift of the index, same instances
--   - encoding: weights $v_{ij}$ on undirected pairs → `v : Sym2 (Fin n) → ℝ`; reason: symmetry by construction; the diagonal is never read
--   - encoding: a fair coin flipped when an undetermined vertex is processed in step 2(c) → one coin per vertex, `ω : Fin n → Bool`, uniform, read only in step 2(c); reason: unread coins change nothing, so the distribution is the same
--   - reading: "Process events at time $t$", with no order within a period → the arrival is processed before the criticality; reason: the edge $(i,i+d)$ exists and the proof bids on it; critical-first makes the theorem false ($n=2$, $d=1$, $v=1$ gives $\mathrm{PG}=0$, $\mathrm{OFF}=1$)
--   - reading: no stated end of the run → the run lasts $n+d$ periods; reason: every vertex must become critical; stopping at $n$ collects nothing on $n=2$, $d=2$
--   - reading: $\operatorname{argmax}$ with no tie-breaking rule → every rule `tie` choosing a maximizer as a function of the arriving vertex, the seller set and the sellers' margins, which sees no coin and no other part of the history; reason: the proof uses no property of the rule, and $p^f$ must not depend on the coins; a deterministic argmax over the margins is such a rule; one fixed rule would be weaker
--   - reading: the input is the online graph $G_{d,\sigma}$ → margins read `onlineWeight`, which is $0$ off the edges of $G_{d,\sigma}$; reason: p.6: "seller $s_k$ does not have any edges" on arrival; a seller past its deadline has no edge to a later buyer
-- source:
--   Ashlagi, Burq, Dutta, Jaillet, Saberi & Sholley, Maximum Weight Online Matching with Deadlines, arXiv:1808.03526v1, Theorem 3.3, proof, p.7, (Offline Dual) and "is a feasible solution to (Offline Dual)"

import Definitions.Def_WindowedMatching_PostponedGreedy

namespace WindowedMatching

/-- `{p^f(s_k) + q(b_k)}_{k ∈ [1,T]}` is a feasible solution to (Offline Dual)
(arXiv:1808.03526v1, §3.2, proof of Theorem 3.3, p.7): `λ_k ≥ 0`, and `v_kl ≤ λ_k + λ_l` for all
`(k, l)` with `|k − l| ≤ d`.

**Formalization Note.** The constraint of (Offline Dual) is stated on edges of `windowGraph n d`, so
on `k ≠ l`. The page's `∀(k, l) s.t. |k − l| ≤ d` formally includes `k = l`, but the program is the
dual of a matching problem, which has no loops. -/
theorem dual_feasible {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) (ω : Fin n → Bool) :
    (∀ k, 0 ≤ (finalState d v tie ω).p k + (finalState d v tie ω).q k) ∧
    (∀ k l, (windowGraph n d).Adj k l →
      v s(k, l) ≤ ((finalState d v tie ω).p k + (finalState d v tie ω).q k) +
        ((finalState d v tie ω).p l + (finalState d v tie ω).q l)) := by sorry

end WindowedMatching
