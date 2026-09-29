-- Prove2me | Theorems.Thm_KServer_chunk_combining_zero_floor_antitone
-- name    : KServer.chunk_combining_zero_floor_antitone
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-07T23:36:00.533062+00:00
-- url     : https://prove2.me/theorems/478bb8c0-7fa4-4a48-b884-b070a8ac2728
-- title:
--   Regrouping at size floor zero, assuming the conditional future mass is non-increasing
-- statement:
--   Let $C$ be a chunk system with online escapes whose sizes lie in $[0,c_B]$ — **size floor zero** — with trivial initial information, no empty chunk, a pointwise Doob jump bound $jb$ on the martingale of its total, and one further regularity property: its conditional future mass
--   $$F_h=\mathbb E\Bigl[\sum_{j\ge h}c_j\ \Bigm|\ \mathcal F_h\Bigr]$$
--   is **non-increasing along every branch**.
--
--   **Statement.** Writing $\mu$ for the expected total divided by $M$, the chunks regroup into a system with exactly $M$ chunks whose sizes all lie in any window containing $[\mu-(c_B+jb),\ \mu+(c_B+jb)]$, with the same expected total, escape price $p'\ge p_e+\mu+c_B+jb$, trivial initial information and no empty chunk.
--
--   **Relation to the existing regrouping lemma.** `KServer.chunk_combining_strong` proves the same conclusion under a *positive* size floor $c_A$ together with $jb\le c_A$. Those two hypotheses are exactly what makes the conditional future mass non-increasing, by `ChunkSystemB.condFuture_antitone`; so the present statement is a strict generalization, obtained by keeping only the consequence that the proof uses and dropping the floor entirely.
--
--   **Why the floor has to go.** The level steps of the $\Omega(\log^2k)$ construction, `KServer.level_step_sturdy` and `KServer.level_step_full`, both consume and produce systems with size floor $0$ — the race genuinely creates chunks of size zero — and a floor cannot be raised afterwards, since `KServer.ChunkSystemB.adjust` only lowers one. So the regrouping that carries the induction from one level to the next has to accept floor zero, and `chunk_combining_strong` cannot.
--
--   **What this statement settles, and what it leaves open.** Its proof shows that the whole of the positive-floor argument survives at floor zero once monotonicity of $F$ is assumed separately: the target levels and the boundary stopping times only need the expected total to be nonnegative, which holds because the sizes are; the boundaries still increase strictly, from the slack $c_B+jb<\mu$ alone; and the last boundary is pinned to the final chunk by definition, the last window then having conditional size in $[\mu-(c_B+jb),\mu]$. Monotonicity of $F$ is used in exactly one place, the escape-price charging, where the conditional future mass at the moment the escape rule fires is compared with its value at the start of the window.
--
--   That single use is also the reason this statement does not yet close the recursion. A system produced by a level step need not have $F$ non-increasing: revealing a coin of the race can raise the expected remaining mass by more than the chunk just consumed. Removing the hypothesis therefore requires redoing the charging in the manner of the source, which charges the escape price to the subchunk during which the algorithm escapes and a fake cost conditioned at the *window start* to each subsequent subchunk, never evaluating the conditional future mass at the firing time. `KServer.chunk_combining_zero_floor` is that hypothesis-free statement.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The randomized k-server conjecture is false!, STOC 2023, https://arxiv.org/abs/2211.05753, Lemma 15 (pp. 19-21). Generalization of the platform theorem KServer.chunk_combining_strong, replacing its positive size floor and the condition jb <= floor by the consequence of those two that the argument actually uses.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond

namespace KServer

theorem chunk_combining_zero_floor_antitone {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ}
    (C : ChunkSystemB X s t 0 cB T pe mL)
    (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω')
    (hch : ∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ [])
    {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS)
    (hanti : ∀ (h h' : ℕ) (ω : C.Ω), h ≤ h' → C.condFuture h' ω ≤ C.condFuture h ω)
    (hcB : 0 ≤ cB)
    {M : ℕ} (hM0 : 0 < M) {cLo' cHi' p' : ℝ}
    (hlo0 : 0 < cLo')
    (hlo : cLo' ≤ (∑ ω, C.P ω * ∑ i, C.size ω i) / M - (cB + jbS))
    (hhi : (∑ ω, C.P ω * ∑ i, C.size ω i) / M + (cB + jbS) ≤ cHi')
    (hp : pe + ((∑ ω, C.P ω * ∑ i, C.size ω i) / M + (cB + jbS)) ≤ p') :
    ∃ C' : ChunkSystemB X s t cLo' cHi' T p' M,
      C'.m = M ∧ (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) := by sorry

end KServer
