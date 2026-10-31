-- Prove2me | Definitions.Def_KServer_binary_read_trace
-- name    : KServer_binary_read_trace
-- status  : Definition
-- author  : @kwal0203
-- created : 2026-10-30T17:44:30.631591+00:00
-- url     : https://prove2.me/theorems/b1427589-e914-4f97-a392-27bd66032400
-- title:
--   Transcript of adaptive Boolean seed reads
-- statement:
--   Let $I$ index Boolean seed coordinates, let $x:I\to\{0,1\}$ be a seed assignment, and let a selection rule choose a coordinate from the current time and transcript. The transcript starts with all entries false. At time $t$, the rule chooses a coordinate using the previous transcript, reads its seed bit, and records that bit at transcript position $t$:
--
--   $$T_x^0(k)=0,\qquad T_x^{t+1}=T_x^t\bigl[t\leftarrow x(\operatorname{choose}(t,T_x^t))\bigr].$$
--
--   This definition records an adaptive sampling program without assuming a probability distribution on the seeds. It can represent a finite prelude followed by the left/right choices of the BCR race. Unwritten transcript positions remain at their initial values.
--
--   **Formalization Note** The transcript is a total function on natural indices. The recursion performs one update per step; causality with respect to a grading of seed coordinates is established by a separate theorem.
-- source:
--   Auxiliary finite sampling formalization for Bubeck–Coester–Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4.1, stage 2a, the adaptive left/right selection rule. This transcript implementation is an auxiliary definition rather than a verbatim definition in the paper.

import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Basic

namespace KServer

/-- The transcript of an adaptive sequence of Boolean seed reads. At time
`n`, the program chooses a coordinate using the previous transcript, reads
that seed bit, and records it at transcript position `n`. -/
def binaryReadTrace {ι : Type*} (choose : ℕ → (ℕ → Bool) → ι)
    (seed : ι → Bool) : ℕ → (ℕ → Bool)
  | 0 => fun _ => false
  | n + 1 => Function.update (binaryReadTrace choose seed n) n
      (seed (choose n (binaryReadTrace choose seed n)))

end KServer


