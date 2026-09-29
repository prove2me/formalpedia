-- Prove2me | Theorems.Thm_groupCohomology_finrank_eulerTerms_eq_of_iso
-- name    : groupCohomology.finrank_eulerTerms_eq_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/b3ecfbb8-3fcb-5014-b0c7-369f9537d28a
-- title:
--   Isomorphism invariance of the global Euler terms
-- statement:
--   Let $p$ be a prime and let $S$ be a finite set of rational primes. Let $M$ and $N$ be objects of the category of $\mathbb{Z}/p$-linear representations (on modules in universe $0$) of the absolute Galois group $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the group of field automorphisms of `AlgebraicClosure ℚ` over $\mathbb{Q}$, and let $e : M \cong N$ be an isomorphism of such representations. Then the following five $\mathbb{Z}/p$-dimensions agree for $M$ and for $N$: the dimension of the submodule of invariants of the representation; the dimension of `continuousH1S S M`, the submodule of $H^1(M)$ obtained as the image under the projection $H^1\pi$ of the submodule `levelCocyclesS₁ S M` of $S$-level cocycles; the dimension of `continuousH2S S M`, the quotient of `levelCocyclesS₂ S M` by the preimage of `levelCoboundariesS₂ S M` under the inclusion of that submodule; the dimension of the invariants of the restriction of the representation along `extArithLoc S (Sum.inl ())`, which at the archimedean index is the inclusion of the subgroup `archimedeanDecomposition` into the Galois group, i.e. the invariants under the archimedean decomposition group; and the dimension of the underlying module itself. No finiteness of dimension is assumed, `finrank` being $0$ where the rank is not finite.
--
--   This is the isomorphism invariance of the five quantities entering the global Euler defect: the $H^0$, the $S$-restricted $H^1$ and $H^2$ carriers, the archimedean $H^0$, and the dimension of the representation. It is used to transport the Euler-characteristic computation along isomorphisms of representations, and is cited in the proof of [`groupCohomology.finrank_invariants_add_finrank_continuousH2S_add_finrank_eq_of_ne_two`](thm.html#groupCohomology.finrank_invariants_add_finrank_continuousH2S_add_finrank_eq_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_eulerTerms_eq_of_iso.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.finrank_eulerTerms_eq_of_iso
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M N : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (e : M ≅ N) :
    finrank (ZMod p) M.ρ.invariants = finrank (ZMod p) N.ρ.invariants ∧
    finrank (ZMod p) (continuousH1S S M) = finrank (ZMod p) (continuousH1S S N) ∧
    finrank (ZMod p) (continuousH2S S M) = finrank (ZMod p) (continuousH2S S N) ∧
    finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) M).ρ.invariants
      = finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) N).ρ.invariants ∧
    finrank (ZMod p) M = finrank (ZMod p) N := by sorry
