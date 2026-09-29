-- Prove2me | Theorems.Thm_groupCohomology_finsum_finrank_invariants_twist_inv_add_eq_index_mul
-- name    : groupCohomology.finsum_finrank_invariants_twist_inv_add_eq_index_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/4c5f2fc3-9f95-5ad6-b45e-23138810cd21
-- title:
--   Archimedean sum splits between N and N(-1)
-- statement:
--   Fix a prime $p$, a finite set $S$ of rational primes, and intermediate fields $K \le L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, each satisfying `IsUnramifiedOutside S`: finite-dimensional over $\mathbb{Q}$ and such that for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the fixing subgroup of the field. Assume the fixing subgroup of $L$ is stable under conjugation by elements of the fixing subgroup of $K$, that the relative index of the fixing subgroup of $L$ in that of $K$ is coprime to $p$, that $L$ contains a primitive $p$-th root of unity $\zeta$, and that if $p = 2$ then $L$ contains a square root of $-1$. Let $N$ be a finite-dimensional $\mathbb{Z}/p$-representation of $\mathrm{Gal}(\overline{\mathbb{Q}}/K)$ on which every element lying in $\mathrm{Gal}(\overline{\mathbb{Q}}/L)$ acts trivially. Then, summing over the orbits $v$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/K)$ on $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})/\mathrm{image}(\mathtt{archimedeanLoc})$, the quantity $\dim_{\mathbb{Z}/p} \bigl(N \otimes \chi^{-1}\bigr)^{D_v} + \dim_{\mathbb{Z}/p} N^{D_v}$, with $\chi$ the mod $p$ cyclotomic character `cycloChar p` restricted to $\mathrm{Gal}(\overline{\mathbb{Q}}/K)$ and $D_v$ the stabiliser of a chosen representative of $v$, adds up to $[\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) : \mathrm{Gal}(\overline{\mathbb{Q}}/K)] \cdot \dim_{\mathbb{Z}/p} N$.
--
--   This computes the archimedean contribution to Tate's global Euler–Poincaré characteristic formula in the case of a module coinduced from a subgroup cut out by an $S$-level, the point being that at a real place the two invariant spaces occurring are the $\mp 1$-eigenspaces of the involution by which complex conjugation acts, since the mod $p$ cyclotomic character sends a complex conjugation to $-1$. It is used in [`groupCohomology.finiteDimensional_continuousH2S_coind_and_finrank_eq`](thm.html#groupCohomology.finiteDimensional_continuousH2S_coind_and_finrank_eq), where the second cohomology of the coinduced module is shown to be finite-dimensional with a prescribed dimension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finsum_finrank_invariants_twist_inv_add_eq_index_mul.lean

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

theorem groupCohomology.finsum_finrank_invariants_twist_inv_add_eq_index_mul
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S) (hL : L.IsUnramifiedOutside S)
    (hKL : K ≤ L)
    (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L)
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (htriv : ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup → N.ρ s = 1) :
    ∑ᶠ v : Quotient (MulAction.orbitRel ↥K.fixingSubgroup
        ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (extArithLoc S (Sum.inl ())).range)),
      (Module.finrank (ZMod p) (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) v.out).subtype
          (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)⁻¹)).ρ.invariants +
        Module.finrank (ZMod p) (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) v.out).subtype N).ρ.invariants) =
      K.fixingSubgroup.index * Module.finrank (ZMod p) N := by sorry
