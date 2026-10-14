-- Prove2me | Theorems.Thm_KServer_workFnU_isometry_embedding
-- name    : KServer.workFnU_isometry_embedding
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T17:40:39.764111+00:00
-- url     : https://prove2.me/theorems/8e7a0e11-0824-42e5-a36b-ea7aef348d0c
-- title:
--   Work functions are preserved by isometric embeddings
-- statement:
--   Let $k\ge1$, and let $e:M\to N$ preserve distances between metric spaces. For every initial configuration, finite request sequence, and terminal configuration in $M$,
--   $$
--   \widehat w^{N}_{eC_0,e\sigma}(eX)=\widehat w^{M}_{C_0,\sigma}(X).
--   $$
--   Surjectivity is not required. Although schedules in $N$ may use additional points, they cannot improve the work function for these data. The backward recurrence eliminates requests one by one, using only replacement of a terminal coordinate by a request; at the empty sequence the value is the distance from the initial configuration. Each operation is preserved by the embedding. Taking the finite infimum over terminal permutations proves the unordered assertion. The initial and terminal configurations may have repetitions, and the spaces need not be finite or compact.
-- source:
--   Work-function recurrence in E. Koutsoupias, The k-server problem (2009), Section 3.4, https://users.cs.fiu.edu/~giri/teach/6936/S10/K-Server_CSReviews_09.pdf. The two recurrence inequalities are reused from Shuze Chen's proved formalizations. Finite-support consequence of the recurrence, proved here. Compare the X-lazy schedule observation in Y. Emek, P. Fraigniaud, A. Korman, A. Rosen, On the Additive Constant of the k-server Work Function Algorithm (2009), Section 2, https://arxiv.org/pdf/0902.1378. The exact uniform-constant transfer below is a separate argument.

import Definitions.Def_KServer_workfunctionU
open KServer

theorem KServer.workFnU_isometry_embedding (k : ℕ) (hk : 1 ≤ k) (M N : Type)
    [MetricSpace M] [MetricSpace N] (e : M → N)
    (he : ∀ x y, dist (e x) (e y) = dist x y)
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    workFnU (fun i => e (C₀ i)) (σ.map e) (fun i => e (X i)) =
      workFnU C₀ σ X := by sorry
