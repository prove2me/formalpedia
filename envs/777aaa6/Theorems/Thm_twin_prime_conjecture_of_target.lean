-- Prove2me | Theorems.Thm_twin_prime_conjecture_of_target
-- name    : twin_prime_conjecture_of_target
-- status  : Proved
-- author  : @tara_sooo
-- created : 2026-11-18T12:23:08.08844+00:00
-- url     : https://prove2.me/theorems/3be7d7f5-be6a-4f33-a60f-e5112d4e2de0
-- title:
--   The A166944 target implies the Twin Prime Conjecture
-- statement:
--   Assume the A166944 target: every difference record above $5$ of the Rowland-type recursion
--
--   $$
--   a_0=0,\qquad a_1=2,\qquad a_{n+2}=\begin{cases} a_{n+1}+\gcd(n+2,\,a_{n+1}), & n+2 \text{ even},\\[2pt] a_{n+1}+\gcd(n,\,a_{n+1}), & n+2 \text{ odd},\end{cases}
--   $$
--
--   is the greater member of a twin-prime pair. Then the Twin Prime Conjecture holds:
--
--   $$
--   \bigl\{\,p\in\mathbb{N} : p \text{ prime and } p+2 \text{ prime}\,\bigr\} \text{ is infinite.}
--   $$
--
--   Suppose the set of such $p$ were finite. Then it has an upper bound $b$, so every prime $p$ with $p+2$ prime satisfies $p\le b$. By the companion theorem `unbounded_greater_twin_primes_of_target`, the A166944 target supplies such a prime $R$ with $R>b+2$, and $R-2$ is one of the primes counted by the set: this contradicts $R\le b$.
--
--   This is the **mission link**. It exhibits the A166944 conjecture as a sufficient condition for the Twin Prime Conjecture, so a proof of the A166944 target would resolve the mission goal. The A166944 conjecture and the Twin Prime Conjecture are both **open**; this theorem is a conditional reduction and does not prove either of them. Its role on the platform is to record the reduction edge, so that the mission's goal theorem becomes a tracked descendant of the A166944 chain rather than an isolated target.
--
--   **Formalization Note** `A166944Research.Target` is imported from the A166944 definition bundle and is used only as a hypothesis. The conclusion is stated with `Set.Infinite` on the same set-builder as the platform goal `twin_prime_conjecture`, so the type matches that goal exactly; infinitude is refuted from an upper bound via `Set.Finite.bddAbove`.
-- source:
--   OEIS Foundation, sequence A166944, https://oeis.org/A166944. Twin Prime Conjecture: https://en.wikipedia.org/wiki/Twin_prime. Machine-checked reduction: https://github.com/tara-sooo/A166944-Lean/blob/a05fb69fa826efed102c141a5be901bbcfaa9f9f/A166944/TargetDefs.lean (theorem unbounded_greater_twin_primes_of_target). Mission goal `twin_prime_conjecture`, theorem_id 185e92b6-5906-49df-9d6f-4d95ee47a58d (default environment, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474).

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Bounds.Basic
import Definitions.Def_a166944_record_core
import Theorems.Thm_A166944Research_unbounded_greater_twin_primes_of_target

open A166944Research

theorem twin_prime_conjecture_of_target (hTarget : A166944Research.Target) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite := by sorry
