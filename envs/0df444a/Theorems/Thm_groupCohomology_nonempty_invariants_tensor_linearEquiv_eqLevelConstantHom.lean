-- Prove2me | Theorems.Thm_groupCohomology_nonempty_invariants_tensor_linearEquiv_eqLevelConstantHom
-- name    : groupCohomology.nonempty_invariants_tensor_linearEquiv_eqLevelConstantHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/65e03d6c-1937-56a2-be3e-1996a63a02bc
-- title:
--   Invariants of C ⊗ N as equivariant level-constant maps
-- statement:
--   Fix a prime $p$ (as a `Fact`), a finite set $S$ of rational primes, a group $\Gamma$ in the zeroth universe with a normal subgroup $Sg$, a homomorphism $r \colon \Gamma \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, a character $\chi \colon \Gamma \to (\mathbb{Z}/p)^{\times}$, and two representations $C, N$ of $\Gamma$ over $\mathbb{Z}/p$, with $N$ finite-dimensional over $\mathbb{Z}/p$. Assume given a $\mathbb{Z}/p$-linear isomorphism $e$ from $C$ onto the submodule `levelConstantHom` of maps $Sg \to \mathbb{Z}/p$, that is, the maps $\varphi$ with $\varphi(st) = \varphi(s) + \varphi(t)$ for all $s,t \in Sg$ which satisfy the predicate `IsLevelConstantSr₁` for the restriction $r \circ Sg.\mathrm{subtype}$ and the set $S$; and assume the twisted equivariance hypothesis $he$: for all $g \in \Gamma$, $x \in C$ and $s,t \in Sg$ with $g^{-1} s g = t$ one has $e(\rho_C(g)x)(s) = \chi(g) \cdot e(x)(t)$. The conclusion asserts that the type of $\mathbb{Z}/p$-linear equivalences between the $\Gamma$-invariants of the representation on the tensor product $C \otimes N$ in $\mathrm{Rep}_{\mathbb{Z}/p}(\Gamma)$ and the submodule `eqLevelConstantHom` $r\,S\,Sg\,(N.\mathrm{twist}\,\chi)$ of maps $Sg \to N$ is nonempty; the latter consists of those $\varphi \colon Sg \to N$ which are additive, satisfy `IsLevelConstantSr₁` for $r \circ Sg.\mathrm{subtype}$ and $S$ with values in $N$, and obey $\chi(g) \cdot \rho_N(g)(\varphi(t)) = \varphi(s)$ whenever $g^{-1} s g = t$. Only the existence of such an equivalence is asserted, no particular map being named.
--
--   This is the coefficient-moving step in the identification of restricted cohomology classes with level-constant homomorphisms: having described $C$ as the additive $S$-level-constant $\mathbb{Z}/p$-valued characters of $Sg$, $\chi$-equivariantly, it computes $(C \otimes N)^{\Gamma}$ as the $\Gamma$-equivariant $S$-level-constant maps $Sg \to N$ with coefficients twisted by $\chi$. It is used in the comparison of the dimension of the restricted-inflated $H^1_S$ with that of the invariants of a Selmer representation tensored with $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_nonempty_invariants_tensor_linearEquiv_eqLevelConstantHom.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_GroupCohomology_LevelConstantHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain
open scoped Classical NumberField NumberField.LevelArith

theorem groupCohomology.nonempty_invariants_tensor_linearEquiv_eqLevelConstantHom
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) {Γ : Type} [Group Γ] (Sg : Subgroup Γ) [Sg.Normal]
    (r : Γ →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (χ : Γ →* (ZMod p)ˣ)
    (C N : Rep.{0} (ZMod p) Γ) [FiniteDimensional (ZMod p) N]
    (e : C ≃ₗ[ZMod p] ↥(levelConstantHom (r.comp Sg.subtype) S (ZMod p) (ZMod p)))
    (he : ∀ (g : Γ) (x : C) (s t : ↥Sg), (g⁻¹ * s * g : Γ) = t →
      (e (C.ρ g x) : ↥Sg → ZMod p) s = ((χ g : (ZMod p)ˣ) : ZMod p) * (e x : ↥Sg → ZMod p) t) :
    Nonempty ((C ⊗ N : Rep.{0} (ZMod p) Γ).ρ.invariants ≃ₗ[ZMod p] ↥(eqLevelConstantHom r S Sg (N.twist χ))) := by sorry
