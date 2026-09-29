-- Prove2me | Theorems.Thm_CliqueComplexFlag_cliqueComplex_galois
-- name    : CliqueComplexFlag.cliqueComplex_galois
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:08:58.398765+00:00
-- url     : https://prove2.me/theorems/e14e138e-b1cf-4a6f-bac4-ce1dfd626e99
-- title:
--   The Galois adjunction `Δ G ⊆ K ↔ G ≤ sk K` for a flag complex `K`
-- statement:
--   **The Galois adjunction `Δ G ⊆ K ↔ G ≤ sk K`** for a flag complex `K`
--   containing all singletons.  This exhibits `Δ ⊣ sk` as a genuine adjunction onto
--   the flag complexes.
--
--   ```lean
--   theorem CliqueComplexFlag.cliqueComplex_galois{K : ASC V} (hflag : IsFlag K)
--       (hsing : ∀ v : V, ({v} : Finset V) ∈ K.faces) (G : SimpleGraph V) :
--       (cliqueComplex G).faces ⊆ K.faces ↔ G ≤ oneSkeleton K := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/RamseyTheory/CliqueComplexGalois.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/RamseyTheory/CliqueComplexGalois.lean#L96

-- Thm stub generated from Geometry/RamseyTheory/CliqueComplexGalois.lean
import Mathlib
import Definitions.Def_Geometry_RamseyTheory_CliqueComplexFlag
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

theorem CliqueComplexFlag.cliqueComplex_galois{K : ASC V} (hflag : IsFlag K)
    (hsing : ∀ v : V, ({v} : Finset V) ∈ K.faces) (G : SimpleGraph V) :
    (cliqueComplex G).faces ⊆ K.faces ↔ G ≤ oneSkeleton K := by sorry
