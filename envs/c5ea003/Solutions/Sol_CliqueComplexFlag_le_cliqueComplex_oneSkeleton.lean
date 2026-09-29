-- Prove2me | solution 1 for CliqueComplexFlag.le_cliqueComplex_oneSkeleton
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:52:41.229855+00:00
-- url     : https://prove2.me/submissions/604d7b74-c0df-4a26-856c-c559230dc93b

-- Sol generated from Geometry/RamseyTheory/CliqueComplexGalois.lean
import Mathlib
import Definitions.Def_Geometry_RamseyTheory_CliqueComplexFlag
import Theorems.Thm_CliqueComplexFlag_mem_cliqueComplex
import Theorems.Thm_CliqueComplexFlag_oneSkeleton_adj
/-
# The One-Skeleton / Clique-Complex Galois Connection

Building on `Catalog/Geometry/CliqueComplexFlag.lean`, this file develops the
order-theoretic backbone of the clique-complex construction.  The two functors

* `cliqueComplex : SimpleGraph V → ASC V`   (denoted `Δ`), and
* `oneSkeleton  : ASC V → SimpleGraph V`    (denoted `sk`),

form a Galois connection between the poset of simple graphs (ordered by `≤`) and
the poset of abstract simplicial complexes (ordered by face inclusion).

## Main results

* `cliqueComplex_mono`             — `Δ` is monotone in the graph.
* `oneSkeleton_mono`              — `sk` is monotone in the complex.
* `le_cliqueComplex_oneSkeleton` — the unit `K ⊆ Δ(sk K)`, needing only downward closure.
* `cliqueComplex_oneSkeleton_idem` — `Δ(sk(Δ G)) = Δ G`, the closure law.
* `cliqueComplex_galois`         — the adjunction `Δ G ⊆ K ↔ G ≤ sk K` for flag
                                    complexes containing all singletons.

-- !-- Lab Notebook -- !--
Hypothesis: `oneSkeleton ∘ cliqueComplex = id` and `flag_eq_cliqueComplex` are
  the two halves of a Galois connection `Δ ⊣ sk` between graphs and complexes.
Result: proved monotonicity of both functors, the unconditional unit
  `K ⊆ Δ(sk K)`, idempotence of the closure `Δ ∘ sk` on images of `Δ`, and the
  full adjunction on flag complexes with all singletons.
Insight: the unit needs ONLY downward closure (every face's pairs are faces, so a
  face is a clique of its own one-skeleton); the counit/adjunction needs the flag
  axiom plus singletons to rebuild a face from its edges.  The two sides of the
  Galois connection are exactly "downward closure" vs. "flagness".
Failure analysis: the adjunction is genuinely conditional — without singletons the
  reverse inclusion fails (see `flag_not_cliqueComplex_without_singletons` in the
  base file), so the connection is an *insertion* only onto the flag complexes.
-- !-- Lab Notebook -- !--
-/

open CliqueComplexFlag

open scoped Classical

universe u
variable {V : Type u}

/-! ## Monotonicity of the two functors -/



/-! ## The unit of the adjunction -/


/-! ## The closure operator `Δ ∘ sk` -/


/-! ## The Galois adjunction -/



open CliqueComplexFlag in
theorem solution(K : ASC V) :
    K.faces ⊆ (cliqueComplex (oneSkeleton K)).faces := by
  -- !-- a face `s`: each pair `{u,v} ⊆ s` is a face by downward closure, i.e. an
  --     edge of `sk K`, so `s` is a clique in `sk K`. -- !--
  intro s hs
  rw [mem_cliqueComplex, SimpleGraph.isClique_iff]
  intro u hu v hv huv
  rw [oneSkeleton_adj]
  refine ⟨huv, K.down_closed ?_ hs⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact_mod_cast hu
  · exact_mod_cast hv
