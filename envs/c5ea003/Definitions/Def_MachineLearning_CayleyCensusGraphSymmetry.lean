-- Prove2me | Definitions.Def_MachineLearning_CayleyCensusGraphSymmetry
-- name    : MachineLearning_CayleyCensusGraphSymmetry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:37:51.596528+00:00
-- url     : https://prove2.me/theorems/2a77b977-f611-4ecc-9881-7b49e3dda7a7
-- title:
--   Aether Catalog definitions — MachineLearning_CayleyCensusGraphSymmetry
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.CayleyCensusGraphSymmetry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/CayleyCensusGraphSymmetry.lean by skeleton subtraction
import Mathlib
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

namespace CayleyCensus

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-! ### Invariance under graph automorphisms fixing the identity -/




/-! ### An invariant of census equivalence -/


/-! ### The converse fails: `K₄,₄` as a Cayley graph on `ℤ/8` -/

open Multiplicative

/-- `ℤ/8` written multiplicatively. -/
abbrev Z8 := Multiplicative (ZMod 8)

/-- The four odd residues; the resulting Cayley graph is `K₄,₄`. -/
def oddSet : Finset Z8 := {ofAdd 1, ofAdd 3, ofAdd 5, ofAdd 7}


/-- The transposition exchanging `2` and `4`.  It fixes the identity and
preserves the bipartition of `K₄,₄`, hence is a graph automorphism; it is not a
group automorphism, since `2` and `4` have different orders. -/
def swap24 : Z8 ≃ Z8 := Equiv.swap (ofAdd (2 : ZMod 8)) (ofAdd (4 : ZMod 8))





end CayleyCensus


