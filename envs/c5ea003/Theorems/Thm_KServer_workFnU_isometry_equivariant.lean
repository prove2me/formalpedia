-- Prove2me | Theorems.Thm_KServer_workFnU_isometry_equivariant
-- name    : KServer.workFnU_isometry_equivariant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T08:05:06.711807+00:00
-- url     : https://prove2.me/theorems/4ad58435-85ac-42a2-bb2e-449fdca36c65
-- title:
--   Isometry-equivariance of the unlabelled work function
-- statement:
--   Let $e \colon M \to N$ be a bijective isometry between metric spaces, and let $w^M$ and $w^N$ denote the unlabelled work functions of the $k$-server instances $(C_0, \sigma)$ on $M$ and $(e \circ C_0, e(\sigma))$ on $N$. Then for every configuration $X$ of $M$,
--
--   $$w^N_{e(\sigma)}(e \circ X) \;=\; w^M_{\sigma}(X).$$
--
--   ## Role
--
--   The unlabelled work function is defined purely in terms of distances — an infimum over schedules of sums of movement costs, followed by an infimum over matchings of the final configuration — so it is invariant under any bijective isometry: pushing schedules forward along $e$ and pulling them back along $e^{-1}$ exhibits a cost-preserving bijection between the two schedule spaces.
--
--   This transfer principle lets statements about work functions proved over a small model (e.g. a metric structure on `Fin n` induced from a finite space) be applied to finite metric spaces in arbitrary universes; it is the bridge used to assemble the $3$-competitiveness of the unlabelled work-function algorithm on trees in universe-polymorphic form.
--
--   ## Formalization note
--
--   The equivalence `e : M ≃ N` carries the bijection and `he` the isometry property; surjectivity of `e` is essential, since otherwise schedules in $N$ could use points outside the image of $e$ and the left-hand side could be smaller.
-- source:
--   Folklore invariance property of the work function (implicit throughout E. Koutsoupias, 'The k-server problem', Computer Science Review 2009); needed here as a universe-transfer bridge.

import Mathlib
import Definitions.Def_KServer_workfunction
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_isometry_equivariant (k : ℕ) (M N : Type*) [MetricSpace M] [MetricSpace N]
    (e : M ≃ N) (he : ∀ x y : M, dist (e x) (e y) = dist x y)
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    workFnU (fun i => e (C₀ i)) (σ.map ⇑e) (fun i => e (X i)) = workFnU C₀ σ X := by sorry

end KServer
