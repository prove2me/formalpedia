-- Prove2me | Theorems.Thm_A166944Research_unbounded_greater_twin_primes_of_target
-- name    : A166944Research.unbounded_greater_twin_primes_of_target
-- status  : Proved
-- author  : @tara_sooo
-- created : 2026-11-18T07:15:52.196219+00:00
-- url     : https://prove2.me/theorems/6d315362-c005-46d6-8bb5-610181c113e2
-- title:
--   Conditional on the A166944 target, arbitrarily large primes $p$ have $p+2$ prime
-- statement:
--   Assume the A166944 target: every difference record of the Rowland-type recursion
--
--   $$
--   a_0=0,\qquad a_1=2,\qquad a_{n+2}=\begin{cases} a_{n+1}+\gcd(n+2,\,a_{n+1}), & n+2 \text{ even},\\[2pt] a_{n+1}+\gcd(n,\,a_{n+1}), & n+2 \text{ odd},\end{cases}
--   $$
--
--   that exceeds $5$ is the greater member of a twin-prime pair. Then arbitrarily large such primes exist:
--
--   $$
--   \forall M\in\mathbb{N}\;\; \exists R\in\mathbb{N},\;\; M<R \;\wedge\; R \text{ prime} \;\wedge\; R-2 \text{ prime}.
--   $$
--
--   The argument combines the two halves of the conjecture. Difference records are unbounded (`difference_records_unbounded`), so above any threshold $M+5$ there is a record $R$; the target applied to that record makes both $R$ and $R-2$ prime, and $R>M$ gives the claim. The constant $M+5$ is bookkeeping for the strict inequality $5<R$ in the target.
--
--   This is the **reduction edge** from the A166944 conjecture to the Twin Prime Conjecture. The conjecture itself is **open**; what is proved here is only the implication, so the statement is a conditional result and does not assert that the twin-prime conjecture has been proved. It is the interface through which any future proof of the target would immediately yield infinitely many twin primes, and it is the theorem to attack if one wants to see the conjecture's reach without engaging its arithmetic core.
--
--   **Formalization Note** `Target` and `IsGreaterTwinPrime` are imported from the A166944 definition bundle: `IsGreaterTwinPrime p` is `p.Prime ∧ (p - 2).Prime`, and `Target` is `∀ R, 5 < R → IsDifferenceRecord R → IsGreaterTwinPrime R`. The hypothesis `hTarget` is an assumption of the theorem, never a proved claim.
-- source:
--   OEIS Foundation, sequence A166944, https://oeis.org/A166944. Machine-checked implication and its target definition: https://github.com/tara-sooo/A166944-Lean/blob/a05fb69fa826efed102c141a5be901bbcfaa9f9f/A166944/TargetDefs.lean (theorem unbounded_greater_twin_primes_of_target, def Target, def IsGreaterTwinPrime). Twin Prime Conjecture background: https://en.wikipedia.org/wiki/Twin_prime. The unconditional statement is the platform theorem `twin_prime_conjecture` (theorem_id a3b92c39-d1c4-4e69-9aca-81bf1d0ce94f in Mathlib 777aaa61; 185e92b6-5906-49df-9d6f-4d95ee47a58d in the default environment).

import Definitions.Def_a166944_record_core
import Mathlib.Data.Nat.Prime.Defs

open A166944Research

namespace A166944Research

theorem unbounded_greater_twin_primes_of_target (hTarget : Target) (M : ℕ) :
    ∃ R : ℕ, M < R ∧ IsGreaterTwinPrime R := by sorry

end A166944Research
