-- Prove2me | solution 1 for CliqueComplexFlag.cliqueComplex_galois
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:52:38.908325+00:00
-- url     : https://prove2.me/submissions/dab5c794-3ff0-4ab3-bae9-9e4e7d3ac8d7

-- Sol generated from Geometry/RamseyTheory/CliqueComplexGalois.lean
import Mathlib
import Definitions.Def_Geometry_RamseyTheory_CliqueComplexFlag
import Theorems.Thm_CliqueComplexFlag_isClique_pair
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
theorem solution{K : ASC V} (hflag : IsFlag K)
    (hsing : ∀ v : V, ({v} : Finset V) ∈ K.faces) (G : SimpleGraph V) :
    (cliqueComplex G).faces ⊆ K.faces ↔ G ≤ oneSkeleton K := by
  -- !-- (→) an edge `u~v` gives a 2-clique `{u,v} ∈ Δ G ⊆ K`, i.e. an edge of `sk K`.
  --     (←) a clique `s` of `G` has all pairs as edges of `sk K`, hence as faces of
  --     `K`; flagness + singletons rebuild `s` as a face. -- !--
  constructor
  · intro h
    rw [SimpleGraph.le_iff_adj]
    intro u v huv
    rw [oneSkeleton_adj]
    have hne : u ≠ v := G.ne_of_adj huv
    refine ⟨hne, h ?_⟩
    rw [mem_cliqueComplex]
    exact (isClique_pair hne).2 huv
  · intro h s hs
    rw [mem_cliqueComplex, SimpleGraph.isClique_iff] at hs
    refine hflag s (fun u _ => hsing u) ?_
    intro u hu v hv huv
    have hadj : G.Adj u v := hs (by exact_mod_cast hu) (by exact_mod_cast hv) huv
    have : (oneSkeleton K).Adj u v := h hadj
    rw [oneSkeleton_adj] at this
    exact this.2
