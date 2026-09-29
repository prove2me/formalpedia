-- Prove2me | Theorems.Thm_KServer_chunk_restrict_sturdy
-- name    : KServer.chunk_restrict_sturdy
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-10T11:28:26.404353+00:00
-- url     : https://prove2.me/theorems/66b75168-8a60-45c9-aa6c-94a3155a4a7f
-- title:
--   Sturdiness by conditioning: defect zero at depth $n$ for $n\\,c_B$ of mass
-- statement:
--   **Sturdiness by conditioning.**
--
--   Let $C$ be a chunk system with online escapes on a metric space $X$ between the marked points $s,t$, with size floor $0$, size ceiling $c_B\ge0$, escape price $p\ge0$ and expected total mass at least $T$, in the sense of `KServer.ChunkSystemB`. Recall that $C$ is *$L^1$-sturdy at depth $n$ with defect $D$* (`KServer.ChunkSystemB.SturdyL1`) when the Doob martingale $D_j$ of the total mass satisfies
--   $$\sum_{\omega}P(\omega)\,\bigl(\mathbb E[\Sigma]-D_j(\omega)\bigr)^{+}\ \le\ D\qquad\text{for all } j\le n,$$
--   i.e. the conditional expected total mass never drops appreciably below its mean during the first $n$ steps of the filtration.
--
--   **Statement.** For every depth $n$ there is a chunk system with the same size floor, size ceiling, escape price and chunk-count bound, with the same number of chunks, whose expected total mass is at least
--   $$T-n\,c_B,$$
--   which is $L^1$-sturdy at depth $n$ with defect $0$, whose initial information is constant, and which has no empty chunk whenever $C$ has none.
--
--   **Content.** Sturdiness with defect $0$ at depth $n$ says that the Doob martingale of the total mass is constant up to time $n$; the statement is that this can always be arranged, for a price of $n$ chunk masses. Condition on the time-$n$ atom $A$ on which the conditional expected total mass is largest — by the tower property that conditional expectation is at least the unconditional mean — and forget the mass of the first $n$ chunks, whose sizes are already known on $A$ and total at most $n\,c_B$ there. On the conditioned system the filtration is trivial up to time $n$, so the Doob martingale is constant up to time $n$ and the defect vanishes.
--
--   Conditioning is legitimate because the cost axiom of a chunk system is stated atom by atom: for a chunk index $i\ge n$ the time-$i$ atoms of the conditioned system are exactly the time-$i$ atoms of the original that lie inside $A$, and both sides of the axiom are simply rescaled by the mass of $A$; for $i<n$ the size has been set to $0$ and the axiom is the nonnegativity of the escape-augmented evader cost.
--
--   **Role.** In the induction of Bubeck--Coester--Rabani's Lemma 12 the level step `KServer.level_step_sturdy` consumes a sturdiness defect $D$ at a depth $n_0$ at least the number $\kappa$ of race steps and charges $-2D$ against the mass it produces. The statement above quantifies the price of manufacturing that hypothesis from nothing: $n\,c_B$ of mass for depth $n$, i.e. one chunk mass per unit of depth, to be compared with the anti-concentration gain of a $\kappa$-step race, which is of order $\sqrt{\kappa}$ chunk masses. So conditioning alone cannot supply the sturdiness needed by a long race, and a regularity invariant has to be carried through the construction instead — this is why the level invariant of the induction has to record more than a two-sided size window.
-- source:
--   Property of the chunk-system model of S. Bubeck, C. Coester, Y. Rabani, The randomized k-server conjecture is false!, STOC 2023, https://arxiv.org/abs/2211.05753 (Section 3, chunk systems, p. 12; Lemma 12, p. 14); the sturdiness invariant is the one consumed by the platform theorem KServer.level_step_sturdy.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_adjust
import Definitions.Def_KServer_sturdy

namespace KServer

/-- **Sturdiness by conditioning.** Every chunk system with size floor zero and
nonnegative escape price can be turned, for any depth `n`, into a chunk system
that is `L¹`-sturdy at depth `n` with defect `0` — its Doob martingale of the
total mass is constant up to time `n` — at the cost of at most `n · cB` of
expected total mass. One conditions on the time-`n` atom on which the
conditional expected total is largest and forgets the mass of the first `n`
chunks. -/
theorem chunk_restrict_sturdy {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ}
    (C : ChunkSystemB X s t 0 cB T pe mL)
    (hpe : 0 ≤ pe) (hcB : 0 ≤ cB) (n : ℕ) :
    ∃ C' : ChunkSystemB X s t 0 cB (T - n * cB) pe mL,
      C'.m = C.m ∧
      C'.SturdyL1 n 0 ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      ((∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ []) →
        ∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) := by sorry

end KServer
