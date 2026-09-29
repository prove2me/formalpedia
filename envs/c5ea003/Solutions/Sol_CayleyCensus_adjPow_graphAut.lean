-- Prove2me | solution 1 for CayleyCensus.adjPow_graphAut
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-20T13:35:18.831792+00:00
-- url     : https://prove2.me/submissions/a1a22da3-ef98-4602-a7db-1ce0e02e02a4

-- Sol generated from MachineLearning/CayleyCensusGraphSymmetry.lean
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




/-! ### An invariant of census equivalence -/


/-! ### The converse fails: `K₄,₄` as a Cayley graph on `ℤ/8` -/

open Multiplicative










open CayleyCensus in
theorem solution{S : Finset G} (φ : G ≃ G)
    (hstep : ∀ x y : G, ((φ x)⁻¹ * φ y ∈ S ↔ x⁻¹ * y ∈ S)) (n : ℕ) (x y : G) :
    (adj S ^ n) (φ x) (φ y) = (adj S ^ n) x y := by
  have hadj : ∀ x y : G, adj S (φ x) (φ y) = adj S x y := by
    intro x y
    show (if (φ x)⁻¹ * φ y ∈ S then 1 else 0) = if x⁻¹ * y ∈ S then 1 else 0
    exact if_congr (hstep x y) rfl rfl
  induction n generalizing x y with
  | zero =>
      simp only [pow_zero, Matrix.one_apply, φ.injective.eq_iff]
  | succ n ih =>
      rw [pow_succ']
      simp only [Matrix.mul_apply]
      rw [← Equiv.sum_comp φ (fun z => adj S (φ x) z * (adj S ^ n) z (φ y))]
      exact Finset.sum_congr rfl fun z _ => by rw [hadj, ih]
