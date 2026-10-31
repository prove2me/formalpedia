-- Prove2me | Theorems.Thm_KServer_binary_read_trace_nonanticipation
-- name    : KServer.binary_read_trace_nonanticipation
-- status  : Proved
-- author  : @kwal0203
-- created : 2026-10-30T17:46:33.943015+00:00
-- url     : https://prove2.me/theorems/7116b010-87dc-4eef-8afc-eb08e78edaeb
-- title:
--   Adaptive Boolean read transcripts depend only on earlier seed levels
-- statement:
--   Let $I$ be any index type for Boolean seeds, and assign each coordinate a natural-number level $g(i)$. An adaptive program starts with an all-false transcript. At step $t$, it chooses a seed coordinate as a function of $t$ and the current transcript, reads that coordinate, and records the resulting bit at transcript position $t$.
--
--   Suppose that for every $t<T$ and every possible transcript $h$,
--
--   $$g(\operatorname{choose}(t,h))=t.$$
--
--   For any $n\le T$, if two seed assignments agree on all coordinates of level below $n$, then their transcripts after $n$ reads agree:
--
--   $$\left(\forall i,\ g(i)<n\Longrightarrow x_i=x'_i\right)\Longrightarrow T_x^n=T_{x'}^n.$$
--
--   This deterministic causality statement supplies freshness for sequential random sampling: changing a coordinate at the current or a later level cannot alter the already produced transcript. It requires no probability distribution, finiteness of the seed index type, or positivity assumptions.
--
--   **Formalization Note** Transcript equality means equality as total Boolean-valued functions on natural indices. The statement includes $n=0$. The level condition is imposed only before the finite horizon.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4.1, stage 2a and stopping rule (1), and Section 4.2, equations (3)–(4), printed pp. 16–19. Deterministic finite-horizon sampling bookkeeping lemma proved here for the auxiliary binaryReadTrace definition; it is not quoted as a separate theorem in the paper.

import Definitions.Def_KServer_binary_read_trace
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open KServer

theorem KServer.binary_read_trace_nonanticipation {ι : Type*} (grade : ι → ℕ)
    (choose : ℕ → (ℕ → Bool) → ι) (N : ℕ)
    (hgrade : ∀ n < N, ∀ history : ℕ → Bool, grade (choose n history) = n)
    (n : ℕ) (hn : n ≤ N) (seed seed' : ι → Bool)
    (hagree : ∀ i, grade i < n → seed i = seed' i) :
    binaryReadTrace choose seed n = binaryReadTrace choose seed' n := by sorry
