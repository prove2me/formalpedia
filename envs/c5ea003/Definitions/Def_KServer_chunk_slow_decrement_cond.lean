-- Prove2me | Definitions.Def_KServer_chunk_slow_decrement_cond
-- name    : KServer_chunk_slow_decrement_cond
-- status  : Definition
-- author  : @Zexuan Liu
-- created : 2026-09-07T23:11:41.147765+00:00
-- url     : https://prove2.me/theorems/45dd9316-c54f-4ab3-b676-dfd2efc430cb
-- title:
--   Slow decrement and bounded surprise, compatible with the filtration API
-- statement:
--   **The two branchwise regularity properties of a chunk system, restated so that they can be used together with the rest of the chunk-system library.**
--
--   For a chunk system with online escapes, write $\mathcal F_h$ for its time-$h$ filtration, $c_j$ for its adapted sizes and
--   $$F_h \;=\; \mathbb E\Bigl[\ \sum_{j\ge h} c_j\ \Bigm|\ \mathcal F_h\Bigr]$$
--   for the conditional expected remaining size, which is `ChunkSystemB.condFuture` of `Def_KServer_chunk_cond`. Two properties are defined here.
--
--   **Slow decrement** with parameter $c_{\max}$: in every branch and at every time,
--   $$F_h - c_{\max}\;\le\;F_{h+1}.$$
--
--   **Bounded surprise** with parameter $c_{\max}$: in every branch and for every window $[a,b)$ of chunk indices,
--   $$\sum_{a\le j<b}c_j\;\le\;F_a-F_b+c_{\max}.$$
--
--   Both hold automatically in conditional expectation; they are branchwise strengthenings, and a regrouping argument that cuts at stopping times consumes them branchwise.
--
--   **Why this restatement is needed.** These properties already exist on the platform, in `Def_KServer_chunk_slow_decrement` and `Def_KServer_chunk_bounded_surprise`. Those files introduce their own copy of the atom map `ChunkSystemB.atom` and their own conditional expectation `ChunkSystemB.condRemaining`, rather than using the ones in `Def_KServer_chunk_cond`. Since a Lean environment cannot contain two declarations with the same name, **no file can import both `Def_KServer_chunk_slow_decrement` and `Def_KServer_chunk_cond`**, and the latter is imported by essentially the whole recursion toolchain: the level steps `KServer.level_step_sturdy` and `KServer.level_step_full`, the regrouping combinators `KServer.chunk_combining_strong` and `KServer.chunk_blocks3`, the window lemmas `KServer.chunk_window_invariants` and `KServer.chunk_window_variance`, and the padding lemmas. The consequence is that `KServer.chunk_regroup_stable`, which is the repaired form of the regrouping step of BCR's Lemma 15 and is proved, cannot be combined in a single proof with the level step whose output it is meant to regroup.
--
--   The definitions here are the same two properties phrased over `condFuture`, so that they compose with the filtration API, with the Doob martingale of the total, with sturdiness, and with the level steps. The window mass is included because bounded surprise refers to it.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The randomized k-server conjecture is false!, STOC 2023, https://arxiv.org/abs/2211.05753, Lemma 15 (pp. 19-21) and the proof of its property 4. Restatement of the platform definitions KServer_chunk_slow_decrement and KServer_chunk_bounded_surprise over the filtration API of KServer_chunk_cond.

import Mathlib
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond

namespace KServer

namespace ChunkSystemB

variable {X : Type*} [MetricSpace X] {s t : X}
variable {cLo cHi total price : ℝ} {mLo : ℕ}
variable (C : ChunkSystemB X s t cLo cHi total price mLo)

/-- **Slow decrement** with parameter `cmax`: along every branch and at every
time, the conditional expected remaining size drops by at most `cmax`.  Stated
over `condFuture` of `Def_KServer_chunk_cond`, so that it can be used together
with the filtration API, the Doob martingale of the total, sturdiness and the
level steps. -/
def SlowDecrementC (cmax : ℝ) : Prop :=
  ∀ (h : ℕ) (ω : C.Ω), C.condFuture h ω - cmax ≤ C.condFuture (h + 1) ω

/-- The realized total size of the chunks whose index lies in the window
`[a, b)`. -/
noncomputable def windowMass (a b : ℕ) (ω : C.Ω) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin C.m => a ≤ (i : ℕ) ∧ (i : ℕ) < b), C.size ω i

/-- **Bounded surprise** with parameter `cmax`: along every branch and across
every window of chunk indices, the realized mass of the window exceeds the drop
of the conditional expected remaining size across that window by at most
`cmax`.  Stated over `condFuture` of `Def_KServer_chunk_cond`. -/
def BoundedSurpriseC (cmax : ℝ) : Prop :=
  ∀ (a b : ℕ) (ω : C.Ω), a ≤ b →
    C.windowMass a b ω ≤ C.condFuture a ω - C.condFuture b ω + cmax

end ChunkSystemB

end KServer


