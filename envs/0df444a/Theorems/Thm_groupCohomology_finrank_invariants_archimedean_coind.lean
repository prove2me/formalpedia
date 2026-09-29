-- Prove2me | Theorems.Thm_groupCohomology_finrank_invariants_archimedean_coind
-- name    : groupCohomology.finrank_invariants_archimedean_coind
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/6d82d526-2c32-5ae7-af8b-5ccc03bd0684
-- title:
--   Mackey decomposition of archimedean invariants of a coinduced module
-- statement:
--   Let $p$ be a prime, let $S$ be a finite set of primes, and let $K$ be an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` that is finite-dimensional over $\mathbb{Q}$; write $\Gamma = \overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ for the absolute Galois group and $\Gamma_K = K$`.fixingSubgroup` for the subgroup fixing $K$ pointwise. Let $N$ be a representation of $\Gamma_K$ over $\mathbb{Z}/p$ on a finite-dimensional $\mathbb{Z}/p$-vector space. The archimedean component `extArithLoc S (Sum.inl ())` of the family of local maps is, by definition, `archimedeanLoc`, the inclusion of the subgroup `archimedeanDecomposition` of $\Gamma$ into $\Gamma$. The assertion is that the $\mathbb{Z}/p$-dimension of the invariants of the restriction along this inclusion of the coinduced representation $\mathrm{coind}_{\Gamma_K}^{\Gamma} N$ (coinduction along the inclusion $\Gamma_K \hookrightarrow \Gamma$) equals the finite sum, indexed by the orbits of $\Gamma_K$ acting on the coset space $\Gamma / D$ with $D$ the range of that inclusion, of the $\mathbb{Z}/p$-dimensions of the invariants of $N$ restricted to the stabiliser in $\Gamma_K$ of a chosen representative `v.out` of each orbit.
--
--   This is the Mackey-type formula computing $H^0$ of a coinduced Galois module at the archimedean place: the $\Gamma_K$-orbits on $\Gamma/D$ index the archimedean places of $K$, and the stabilisers are the corresponding decomposition groups. It feeds the computations of continuous $H^1$ of a cyclotomic twist and of continuous $H^2$ of a coinduced module at an $S$-level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_invariants_archimedean_coind.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation
open scoped Classical

theorem groupCohomology.finrank_invariants_archimedean_coind
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N] :
    Module.finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) (Rep.coind K.fixingSubgroup.subtype N)).ρ.invariants =
      ∑ᶠ v : Quotient (MulAction.orbitRel ↥K.fixingSubgroup
          ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (extArithLoc S (Sum.inl ())).range)),
        Module.finrank (ZMod p) (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) v.out).subtype N).ρ.invariants := by sorry
