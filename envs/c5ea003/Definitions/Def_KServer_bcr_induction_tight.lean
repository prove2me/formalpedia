-- Prove2me | Definitions.Def_KServer_bcr_induction_tight
-- name    : KServer_bcr_induction_tight
-- status  : Definition
-- author  : @Zexuan Liu
-- created : 2026-09-07T21:26:25.186288+00:00
-- url     : https://prove2.me/theorems/4e58d2e9-113b-43bd-b633-f60ab2f17310
-- title:
--   The BCR Lemma 12 level invariant at the tight escape price
-- statement:
--   **The level-$w$ invariant of Bubeck--Coester--Rabani's Lemma 12, in the form the formalized level-step machinery can consume.**
--
--   Let $\mathcal M_w=\mathtt{bcrLevel2}\ \beta\ w$ be the canonical recursive $\Theta$-glued space with marked points $s_w,t_w$ at distance $d_w=\beta\,3^w$. The predicate $\mathrm{ChunksTight}(\alpha,\beta,w)$ asserts that there are a chunk count $M$ and a filtered chunk system with online escapes on $\mathcal M_w$ between $s_w$ and $t_w$ with
--
--   * size window $\bigl[3^w/2,\ 3\cdot 3^w/2\bigr]$,
--   * expected total size at least $\alpha\beta w^2 3^w$,
--   * **escape price $\beta\,3^w=d_w$**,
--   * exactly $M$ chunks, with $M\ge\lceil\alpha\beta w^2\rceil$,
--   * constant initial information,
--   * no empty chunk.
--
--   It differs from `KServer.BCRInductiveChunks` in three respects, each of them a hypothesis that the proved level steps `KServer.level_step_sturdy` and `KServer.level_step_full` require of their input and that the older predicate does not supply.
--
--   **The escape price.** Both level steps assume `hpD : p ≤ dist s t` of the incoming system, whereas `BCRInductiveChunks` fixes the price at $2\beta 3^w=2d_w$. The parameter cannot be repaired after the fact: a chunk system's cost bound is stated against the escape price, so `KServer.ChunkSystemB.adjust` can only *raise* it, never lower it. Consequently no system satisfying `BCRInductiveChunks` can be fed to either level step. Taking the price to be exactly $d_w$ removes the obstruction and is preserved by the recursion, since a level step may output any price at least as large as its input's and the next level has $d_{w+1}=3d_w$.
--
--   **The chunk count.** A level step needs the number of chunks to be *exactly* the type-level parameter $M$; `BCRInductiveChunks` records only the lower bound $\lceil\alpha\beta w^2\rceil\le m$, and `adjust` can lower a count bound but not raise it.
--
--   **Nonempty chunks.** Both the level step and the regrouping combinator `KServer.chunk_combining_strong` require it, and it is what the padding lemmas `KServer.chunk_pad2`--`chunk_pad4` are for.
--
--   The two-sided size window is kept, because `KServer.chunk_window_invariants` and `KServer.chunk_window_variance` convert it directly into the sturdiness defect, the Doob jump bound, the below-floor count and the variance bound that the level step also takes as input, so no further probabilistic hypothesis has to be carried explicitly.
--
--   The invariant is a strengthening of `BCRInductiveChunks`: raising the price to $2d_w$ and forgetting the count and nonemptiness recovers it.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The randomized k-server conjecture is false!, STOC 2023, https://arxiv.org/abs/2211.05753, Lemma 12 (p. 14, properties 1-7; the escape price of property 4 is 2 d_w(s_w,t_w) there). Interface adjusted to the hypotheses of the platform theorems KServer.level_step_sturdy and KServer.chunk_combining_strong.

import Mathlib
import Definitions.Def_KServer_bcr_space2
import Definitions.Def_KServer_chunk_system_b

namespace KServer

/-- The level-`w` invariant of BCR's Lemma 12, stated with the escape price
`d(s_w,t_w) = β·3^w` (rather than twice that), with the exact chunk count and
with nonempty chunks: exactly the interface the proved level-step lemmas
consume and produce. -/
def BCRInductiveChunksTight (α : ℝ) (β : ℕ) (hβ : 0 < β) (w : ℕ) : Prop :=
  ∃ (M : ℕ) (C : @ChunkSystemB (bcrLevel2 β hβ w).carrier (bcrLevel2 β hβ w).metric
      (bcrLevel2 β hβ w).s (bcrLevel2 β hβ w).t
      ((3 : ℝ) ^ w / 2) (3 * (3 : ℝ) ^ w / 2)
      ((α * β * (w : ℝ) ^ 2) * 3 ^ w) ((β : ℝ) * 3 ^ w) M),
    C.m = M ∧ ⌈α * β * (w : ℝ) ^ 2⌉₊ ≤ M ∧
      (∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) ∧
      (∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ [])

end KServer


