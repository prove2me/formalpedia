-- Prove2me | Theorems.Thm_KServer_chunk_system_mapped
-- name    : KServer.chunk_system_mapped
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T14:31:07.89146+00:00
-- url     : https://prove2.me/theorems/3b3126d7-3c05-4f0b-a5ea-c865a063e108
-- title:
--   Mapped chunk systems along projected request transformations
-- statement:
--   **Mapped chunk systems along projected request transformations.** Let $C$ be a chunk system with online escapes on a metric space $X$ with marked points $s, t$, and let $Y$ be another metric space with marked points $a, b$. Suppose given a transformation $G$ of request sets from $X$ to $Y$, a nonexpansive projection $\pi : Y \to X$ with $\pi(G(S)) \subseteq S$ and $G(S)$ nonempty exactly when $S$ is, and a distance-preserving lift $\iota : X \to Y$ with $\iota(S) \subseteq G(S)$, $\iota(s) = a$, $d_X(s,t) \le d_Y(a,b)$, and $G(\{t\}) = \{b\}$. Then transforming every request of $C$ by $G$ yields a chunk system on $Y$ with marked points $a, b$ and the same sample space, filtration, sizes, chunk count, and expected total, at any escape price $p' \ge p_e$; in particular a trivial initial history and a variance bound $$\sum_\omega P(\omega)\Big(\sum_i c_i(\omega) - \mathbb{E}\big[\textstyle\sum_i c_i\big]\Big)^2 \le V$$ carry over verbatim. The cost premises transfer by shadowing: an online evader on $Y$ facing the transformed requests induces, through $\pi$, an online evader on $X$ whose bail-aware cost it dominates; the offline bound transfers through the lift $\iota$. This combinator places the inductive chunk systems of the BCR lower bound into the glued level step: $\iota$ is a copy embedding, $\pi$ the nonexpansive retraction onto that copy, and $G$ places each request into one copy or as a union over two copies.
-- source:
--   BCR randomized k-server lower bound, stage construction layer

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_shadow

namespace KServer

theorem chunk_system_mapped {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {s t : X} {a b : Y} {cA cB T pe pe' : ℝ} {mL : ℕ}
    (C : ChunkSystemB X s t cA cB T pe mL)
    (G : Set X → Set Y) (π : Y → X) (ι : X → Y)
    (hπ : ∀ y z : Y, dist (π y) (π z) ≤ dist y z)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (hGe : ∀ S : Set X, (G S).Nonempty → S.Nonempty)
    (hι : ∀ x x' : X, dist (ι x) (ι x') = dist x x')
    (hGsup : ∀ S : Set X, ι '' S ⊆ G S)
    (hιs : ι s = a)
    (hab : dist s t ≤ dist a b)
    (hlastG : G {t} = {b})
    (hpe : pe ≤ pe')
    {V : ℝ}
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V) :
    ∃ C' : ChunkSystemB Y a b cA cB T pe' mL,
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V) := by sorry

end KServer
