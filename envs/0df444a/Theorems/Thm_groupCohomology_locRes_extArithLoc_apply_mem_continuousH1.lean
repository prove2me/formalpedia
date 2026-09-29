-- Prove2me | Theorems.Thm_groupCohomology_locRes_extArithLoc_apply_mem_continuousH1
-- name    : groupCohomology.locRes_extArithLoc_apply_mem_continuousH1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/bb317386-feff-52b5-b158-65985092c4ec
-- title:
--   Localisation preserves continuous degree-one classes
-- statement:
--   Fix a prime $p$, a finite set $S$ of rational primes, and a representation $M$ of the absolute Galois group $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the group of field automorphisms of `AlgebraicClosure ℚ` over $\mathbb{Q}$, on a module over $\mathbb{Z}/p$. Let $x$ be a class in $H^1(\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}), M)$ which lies in `continuousH1 (MonoidHom.id _) M`, that is, in the image under the projection `H1π` from one-cocycles to $H^1$ of the submodule `levelCocycles₁` of cocycles taken along the identity homomorphism of the global group. Let $v$ be an index of the arithmetic local datum `extArithIndex S`, i.e. either the single archimedean index or an index coming from a prime $q \in S$; the associated local group is the subgroup `archimedeanDecomposition` of the global group in the first case and `primeLocalGaloisGroup q` in the second, and `extArithLoc S v` is the corresponding homomorphism to the global group, namely the subgroup inclusion, respectively [`localGaloisToGlobal`](def/GaloisRep_CompletionBridge.html#L41). The assertion is that the localisation of $x$ at $v$ — its image under `locRes (extArithLoc S) M v`, the map on $H^1$ induced by `extArithLoc S v` together with the identity of the restricted representation `Rep.res (extArithLoc S v) M` — lies in `continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M)`, the image under `H1π` of `levelCocycles₁` taken along `extArithLoc S v`.
--
--   This is the functoriality of continuous (level-constant) degree-one cohomology under restriction along a local-to-global homomorphism: localisation maps the continuous part of the global $H^1$ into the continuous part of each local $H^1$. It is used when the Selmer-type groups attached to the arithmetic local datum on $S$ are set up and compared, being cited in the Greenberg–Wiles computations for `extArithLoc` and in the corresponding statement for localisation at a set of primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_locRes_extArithLoc_apply_mem_continuousH1.lean

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_GroupCohomology_ContinuousH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology ExtCitation

theorem groupCohomology.locRes_extArithLoc_apply_mem_continuousH1
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (x : H1 M) (hx : x ∈ continuousH1 (MonoidHom.id _) M) (v : extArithIndex S) :
    (locRes (extArithLoc S) M v).hom x ∈
      continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) := by sorry
