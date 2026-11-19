-- Prove2me | Theorems.Thm_A166944Research_a166944_record_is_greater_twin_prime
-- name    : A166944Research.a166944_record_is_greater_twin_prime
-- status  : Open
-- author  : @tara_sooo
-- created : 2026-11-18T07:04:27.030501+00:00
-- url     : https://prove2.me/theorems/5a9db4e6-b292-46c0-839f-3cc63d93ee28
-- title:
--   Every A166944 difference record above 5 is the greater member of a twin-prime pair
-- statement:
--   Let $a$ be the Rowland-type recursion of OEIS A166944,
--
--   $$
--   a_1=2,\qquad a_n=a_{n-1}+\begin{cases}\gcd(n,\,a_{n-1}), & n \text{ even},\\[2pt] \gcd(n-2,\,a_{n-1}), & n \text{ odd},\end{cases}
--   $$
--
--   with first differences $d_n=a_n-a_{n-1}$. Call $R$ a **difference record** when $d_n=R$ for some $n\ge2$ and $d_k<R$ for every $2\le k<n$; that is, $R$ is a strict running maximum of $(d_n)$ and is attained.
--
--   The theorem asserts that every such record above $5$ is the larger half of a twin-prime pair:
--
--   $$
--   \forall R\in\mathbb{N},\qquad 5<R \;\wedge\; \bigl(R \text{ is a difference record}\bigr) \;\Longrightarrow\; R \text{ and } R-2 \text{ are both prime}.
--   $$
--
--   The records themselves are known to be unbounded (a companion theorem, `difference_records_unbounded`, proves this), so the statement is not vacuous: it constrains an unbounded sequence of values. Combined with that unboundedness it yields infinitely many twin-prime pairs, which is the sense in which this conjecture is stronger than a mere curiosity about a recursion.
--
--   This is the A166944 conjecture, and it is **open**. Its content is purely arithmetic: the combinatorial half -- that records exist above every threshold -- has already been settled, so what remains is to explain why the record values, which are produced by iterated `gcd` operations with no visible arithmetic input, should always land exactly two below a prime.
--
--   Two structural facts are established elsewhere in this development and are the intended starting points. First, a record value $R$ always divides a definite index: $R\mid n$ when the attaining index is even and $R\mid n-2$ when it is odd, because the increment at $n$ is a `gcd` with that index. Second, at the attaining index the recursion is at a *fundamental point* in the sense that the reservoir coordinate $B_n=a_n-(2n-2)$ vanishes one step earlier; the data show the record value is then forced to be $n-2$. What is missing is a uniform bound on how far the attaining index can lie from the previous record, which is the form in which the obstruction is recorded in the project's `REACH.md`.
--
--   **Formalization Note** Indices are restricted to $\ge2$, the range in which `d` is a genuine difference rather than a truncated subtraction. `IsDifferenceRecord` and `IsGreaterTwinPrime` come from the shared definition bundle `Def_a166944_record_core`, so this statement is stated against exactly the same vocabulary as the companion results.
-- source:
--   OEIS Foundation, sequence A166944, https://oeis.org/A166944 (conjecture of V. Shevelev, 2009). Original statement: V. Shevelev, arXiv:0910.4676, Conjecture 1. Formalization pinned to google-deepmind/formal-conjectures@8323e878b83fcd7f4a448256069352a265460d75, file FormalConjectures/OEIS/166944.lean (theorem `conjecture`). Machine-checked partial results: https://github.com/tara-sooo/A166944-Lean (A166944/RecordBarrier.lean for unboundedness, A166944/TravelReduction.lean and REACH.md for the reduction to an index bound).

import Definitions.Def_a166944_record_core

open A166944Research

namespace A166944Research

theorem a166944_record_is_greater_twin_prime :
    ∀ R : Nat, 5 < R → IsDifferenceRecord R → IsGreaterTwinPrime R := by
  sorry

end A166944Research
