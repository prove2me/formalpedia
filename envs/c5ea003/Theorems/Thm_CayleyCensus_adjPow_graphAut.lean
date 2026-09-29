-- Prove2me | Theorems.Thm_CayleyCensus_adjPow_graphAut
-- name    : CayleyCensus.adjPow_graphAut
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T21:38:10.609486+00:00
-- url     : https://prove2.me/theorems/fdec5da2-d414-4f62-8fd7-bda10d30d469
-- title:
--   A permutation of `G` preserving the `S`-step relation preserves all entries
-- statement:
--   A permutation of `G` preserving the `S`-step relation preserves all entries
--   of all adjacency powers.
--
--   ```lean
--   theorem CayleyCensus.adjPow_graphAut{S : Finset G} (φ : G ≃ G)
--       (hstep : ∀ x y : G, ((φ x)⁻¹ * φ y ∈ S ↔ x⁻¹ * y ∈ S)) (n : ℕ) (x y : G) :
--       (adj S ^ n) (φ x) (φ y) = (adj S ^ n) x y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/CayleyCensusGraphSymmetry.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/CayleyCensusGraphSymmetry.lean#L50

-- Thm stub generated from MachineLearning/CayleyCensusGraphSymmetry.lean
import Mathlib
import Definitions.Def_MachineLearning_CayleyCensusGraphSymmetry
import Definitions.Def_MachineLearning_CayleyCensusMoments

/-!
# Beyond group symmetry: graph automorphisms, and the failure of the converse

`MachineLearning.CayleyCensusInvariance` shows that the census
`walkCount S n g` is invariant under inversion and under `S`-preserving group
automorphisms.  Two natural questions remain, and both are settled here.

**Is group symmetry the only source of census invariance?**  No.  The census is
invariant under every *graph* automorphism of `Cay(G, S)` fixing the identity —
a strictly larger supply of symmetries in general, since such a permutation need
not respect the multiplication of `G` at all.  This is `walkCount_graphAut`,
proved through the adjacency-power bridge `walkCount_eq_adj_pow`: the inductive
step is a reindexing of the intermediate vertex along the permutation.  The
group-automorphism theorem is recovered as the corollary
`walkCount_mulAut_of_graphAut`.

**Is the converse of the main theorem true — do equal census rows force census
equivalence?**  No, and the failure is already visible in a group of order 8.
For `G = ℤ/8` (written multiplicatively) with connection set the four odd
residues, `Cay(G, S)` is the complete bipartite graph `K₄,₄`.  Its census has
exactly two distinct rows,

`n = 0..4`:  `[1,0,0,0,0,0,0,0]`, `[0,1,0,1,0,1,0,1]`, `[4,0,4,0,4,0,4,0]`,
`[0,16,0,16,0,16,0,16]`, `[64,0,64,0,64,0,64,0]`,

whereas `⟨inversion, Aut(G,S)⟩` has four orbits `{0}, {4}, {2,6}, {1,3,5,7}`.
Concretely `2` and `4` have identical censuses but are *not* census-equivalent:
`4` is an involution and `2` is not, and `CensusEquiv_sq_eq_one_iff` shows that
census equivalence must preserve being an involution.  The extra coincidence is
explained instead by the transposition `(2 4)`, a graph automorphism of `K₄,₄`
fixing the identity that is not induced by any group automorphism.

## Main results

* `adjPow_graphAut`, `walkCount_graphAut`
* `walkCount_mulAut_of_graphAut`
* `CensusEquiv_sq_eq_one_iff`
* `census_eq_but_not_censusEquiv` — the converse of the invariance theorem is
  false; the census orbits are strictly coarser than the `⟨inv, Aut(G,S)⟩`
  orbits.
-/

open CayleyCensus

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ### Invariance under graph automorphisms fixing the identity -/

theorem CayleyCensus.adjPow_graphAut{S : Finset G} (φ : G ≃ G)
    (hstep : ∀ x y : G, ((φ x)⁻¹ * φ y ∈ S ↔ x⁻¹ * y ∈ S)) (n : ℕ) (x y : G) :
    (adj S ^ n) (φ x) (φ y) = (adj S ^ n) x y := by sorry
