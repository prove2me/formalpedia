-- Prove2me | Theorems.Thm_groupCohomology_locRes_mem_continuousH1_of_mem_continuousH1S
-- name    : groupCohomology.locRes_mem_continuousH1_of_mem_continuousH1S
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/10351bad-70be-5d5b-acdc-4394d87686a1
-- title:
--   Localisation of an S-level global class is locally continuous
-- statement:
--   Fix a prime $p$, a finite set $S$ of rational primes, and an object $M$ of $\mathrm{Rep}_{\mathbb{Z}/p}(\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}))$, where $\overline{\mathbb{Q}}$ is `AlgebraicClosure ℚ`. Let $x \in H^1(M)$ lie in the submodule `continuousH1S S M`, that is, in the image under the projection `H1π M` of the submodule `levelCocyclesS₁ S M` of one-cocycles. Let $v$ be an index in `extArithIndex S` $= \mathrm{Unit} \sqcup S$, and let `extArithLoc S v` be the associated homomorphism into the global Galois group: for the single archimedean index it is the inclusion of the subgroup `archimedeanDecomposition`, and for an index $q \in S$ it is `primeLocalToGlobal q`, the map [`localGaloisToGlobal`](def/GaloisRep_CompletionBridge.html#L41) from `primeLocalGaloisGroup q` to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$. Then the image of $x$ under the localisation map `locRes (extArithLoc S) M v`, the map on $H^1$ induced by `extArithLoc S v` together with the identity of `Rep.res (extArithLoc S v) M`, lies in `continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M)`, i.e. in the image under `H1π` of the submodule `levelCocycles₁` of one-cocycles of the restricted representation.
--
--   This is the compatibility of the localisation maps with the continuity (level-constancy) conditions: a global class satisfying the $S$-level condition restricts at each place of $\{\infty\} \sqcup S$ to a local class satisfying the level condition defining the local continuous subspace. It supplies the local continuity input for the degree-one Poitou–Tate type statements over the index set `extArithIndex S`, and is used in the construction of the Selmer/Sha pairings over that index set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_locRes_mem_continuousH1_of_mem_continuousH1S.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.locRes_mem_continuousH1_of_mem_continuousH1S
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (x : H1 M) (hx : x ∈ continuousH1S S M) (v : extArithIndex S) :
    (locRes (extArithLoc S) M v).hom x ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) := by sorry
