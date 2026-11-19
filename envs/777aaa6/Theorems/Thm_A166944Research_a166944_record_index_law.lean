-- Prove2me | Theorems.Thm_A166944Research_a166944_record_index_law
-- name    : A166944Research.a166944_record_index_law
-- status  : Open
-- author  : @tara_sooo
-- created : 2026-11-19T05:16:15.603996+00:00
-- url     : https://prove2.me/theorems/5ba896ee-2fe6-466a-9ffd-95f3e3c82325
-- title:
--   The A166944 record-index law: a difference record is attained at $R+2$
-- statement:
--   Let $a$ be the OEIS A166944 recurrence and $d_n=a_n-a_{n-1}$ its first differences. Suppose $R>5$ is a **difference record**: there is $n\ge2$ with $d_n=R$ and $d_k<R$ for every $2\le k<n$.
--
--   Then the record occurs at the canonical index determined by its own value:
--
--   $$n = R+2.$$
--
--   In words, a value that is a strict running maximum of the differences is attained at exactly one place, and that place is $R+2$ -- the canonical start of the replay that the record's own value indexes. This is the **record-index law**.
--
--   Its role is structural. The terminal argument certifies, at a canonical start $M+2$ with $d_{M+2}=M$, that the next difference record is a twin prime. To apply that conclusion to an arbitrary record $R$, one must know that $R$ *is* such a canonical start, and this law supplies exactly that: from the record hypothesis $d_n=R$ alone it recovers $n=R+2$.
--
--   The law is equivalent to a fundamental-return condition, which is how the recurrence side proves it: a canonical record whose next strict record is reached must return to the state $B_n=a_n-2n+2=2$ strictly between them, and conversely such a return pins the index. Either form may be proved; this statement is the index form, which is what the composition consumes.
--
--   **Why it is not a formality.** The canonical index law is not read off the definition: $d_n=R$ alone permits $n$ to be any index where the value $R$ happens to appear, including repetitions after the record was set. Excluding those repetitions is the content, and it uses the divisibility structure of the recurrence: after a record $R$ at $n$, the offsets force $B_{n'}=2$ for some intermediate $n'$, which pins the next occurrence.
-- source:
--   Derived within this development; the Mathlib-side original is CanonicalRecord.record_index_iff_canonical_returns, stated there in the equivalent fundamental-return form. See https://github.com/tara-sooo/A166944-Lean

import Definitions.Def_a166944_record_core

open A166944Research

namespace A166944Research

theorem a166944_record_index_law :
    ∀ {R n : Nat}, 5 < R → 2 ≤ n → d n = R →
      (∀ j : Nat, 2 ≤ j → j < n → d j < R) → n = R + 2 := by
  sorry

end A166944Research
