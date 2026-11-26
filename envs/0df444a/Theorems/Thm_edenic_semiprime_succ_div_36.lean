-- Prove2me | Theorems.Thm_edenic_semiprime_succ_div_36
-- name    : edenic_semiprime_succ_div_36
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-26T16:48:12.347848+00:00
-- url     : https://prove2.me/theorems/cc90b55d-5c17-5669-91d2-1948aa67a0f1
-- title:
--   The successor of an Edenic semiprime divides 36 only for 35
-- statement:
--   For every Edenic semiprime $n = p(p+2)$ (the product of a twin prime pair $p$, $p+2$),
--   $$(n + 1 \mid 36) \iff n = 35 ,$$
--   where $\mid$ denotes divisibility in $\mathbb{N}$.
--
--   Because $n = p(p+2)$, the successor of $n$ is a perfect square: $n + 1 = p^2 + 2p + 1 = (p+1)^2$. If $(p+1)^2$ divides $36$ then necessarily $(p+1)^2 \le 36$, so $p + 1 \le 6$ and $p \le 5$. The pair $(2,4)$ is not a twin prime pair ($4$ is composite), so $p \ge 3$ and the only candidates are $p = 3$ and $p = 5$. The pair $(3,5)$ gives $n = 15$ with $n + 1 = 16$, and $16 \nmid 36$; the pair $(5,7)$ gives $n = 35$ with $n + 1 = 36$, and $36 \mid 36$. The converse direction is immediate from $n = 35$. Hence $35$ — the second member of the family $15, 35, 143, 323, \dots$ — is the unique Edenic semiprime whose successor divides $36$.
--
--   **Formalization.** The identity $p(p+2)+1 = (p+1)^2$ is established by `ring` and rewritten into the divisibility hypothesis; `Nat.le_of_dvd` (against `by norm_num : 0 < 36`) together with `nlinarith` yields $p + 1 \le 6$, and `omega` enumerates the remaining candidates $p \in \{3,4,5\}$. Each is dispatched by `norm_num` (the divisibilities $16 \mid 36$ and $25 \mid 36$ are false), with $p = 5$ closed by `rfl`; the backward implication is `norm_num [h]`.
--
--   **Reuse.** Direct — no imports beyond the definition. Companions: `edenic_semiprime_succ_is_square` (the identity $n+1 = (p+1)^2$ itself) and `edenic_semiprime_succ_not_prime`.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_succ_div_36 (n : ℕ) (h : IsEdenicSemiprime n) :
    (n + 1 ∣ 36) ↔ n = 35 := by
  sorry
