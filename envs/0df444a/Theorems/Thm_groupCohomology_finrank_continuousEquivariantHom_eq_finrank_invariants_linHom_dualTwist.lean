-- Prove2me | Theorems.Thm_groupCohomology_finrank_continuousEquivariantHom_eq_finrank_invariants_linHom_dualTwist
-- name    : groupCohomology.finrank_continuousEquivariantHom_eq_finrank_invariants_linHom_dualTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/76eb761e-0669-56db-9cc0-df99aaec6610
-- title:
--   Equivariant continuous Kummer theory in Hom form
-- statement:
--   Let $\Omega/k$ be an extension of fields which is Galois, write $G=\Omega\simeq_{\mathrm{alg}[k]}\Omega$ for its automorphism group, and let $K$ be an intermediate field, finite-dimensional over $k$, with $g x\in K$ for every $g\in G$ and $x\in K$; let $S=K.\mathrm{fixingSubgroup}$. Fix a prime $p$, a character $\chi:G\to(\mathbb{Z}/p)^\times$, and a unit $\zeta\in\Omega^\times$ which is a primitive $p$-th root of unity, lies in $K$, and satisfies $g\cdot\zeta=\zeta^{(\chi g).\mathrm{val}}$ for all $g\in G$; assume every nonzero $a\in K$ admits $\alpha\in\Omega$ with $\alpha^p=a$. Let $A$ be a representation of $G$ over $\mathbb{Z}/p$, finite-dimensional, with $A.\rho\,s=\mathrm{id}$ for all $s\in S$, and let $W$ be a $\mathbb{Z}/p$-submodule of the $1$-cocycles of $A$ restricted along $S\hookrightarrow G$ characterised by: $c\in W$ if and only if (i) there is an intermediate field $E$, finite-dimensional over $k$, with $c(gs)=c(g)$ for all $g,s\in S$ such that $s$ fixes $E$ pointwise, and (ii) $A.\rho\,g\,(c\,t)=c\,s$ whenever $g\in G$ and $s,t\in S$ satisfy $g^{-1}sg=t$. Let $X$ be a representation of $G$ on a $\mathbb{Z}/p$-module $VX$ together with a surjective map $\pi:(\!K)^\times\to VX$ satisfying $\pi(ab)=\pi a+\pi b$, $\pi a=0$ if and only if $a$ is a $p$-th power in $(\!K)^\times$, and $X\,g\,(\pi a)=\pi b$ whenever $g(a)=b$ in $\Omega$. Then the $\mathbb{Z}/p$-dimension of $W$ equals the $\mathbb{Z}/p$-dimension of the $G$-invariants of the representation on $\mathbb{Z}/p$-linear maps from $A^\vee$ twisted by $\chi$ (the representation $g\mapsto(\chi g)\cdot A.\rho^\vee g$) to $X$.
--
--   This is the $G$-equivariant form of continuous Kummer theory: locally constant, conjugation-equivariant homomorphisms $S\to A$ are matched dimension-for-dimension with $G$-equivariant homomorphisms $A^\vee(\chi)\to K^\times/(K^\times)^p$. It supplies the degree-one term in the tame local Euler-characteristic count used by [`groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField`](thm.html#groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_continuousEquivariantHom_eq_finrank_invariants_linHom_dualTwist.lean

import Mathlib
import Definitions.Def_GroupCohomology_Selmer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Module CategoryTheory groupCohomology

theorem groupCohomology.finrank_continuousEquivariantHom_eq_finrank_invariants_linHom_dualTwist
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K]
    (hKG : ∀ (g : Ω ≃ₐ[k] Ω) (x : Ω), x ∈ K → g x ∈ K)
    {p : ℕ} [Fact p.Prime] (χ : (Ω ≃ₐ[k] Ω) →* (ZMod p)ˣ) {ζ : Ωˣ} (hζp : IsPrimitiveRoot ζ p)
    (hζ : ∀ g : Ω ≃ₐ[k] Ω, g • ζ = ζ ^ (χ g : ZMod p).val) (hζK : (ζ : Ω) ∈ K)
    (hroots : ∀ a : Ω, a ∈ K → a ≠ 0 → ∃ α : Ω, α ^ p = a)
    (A : Rep.{0} (ZMod p) (Ω ≃ₐ[k] Ω)) [FiniteDimensional (ZMod p) A]
    (htriv : ∀ s ∈ K.fixingSubgroup, ∀ v : A, A.ρ s v = v)
    (W : Submodule (ZMod p) (cocycles₁ (Rep.res K.fixingSubgroup.subtype A)))
    (hW : ∀ c, c ∈ W ↔
      (∃ E : IntermediateField k Ω, FiniteDimensional k E ∧
        ∀ (g s : K.fixingSubgroup), (s : Ω ≃ₐ[k] Ω) ∈ E.fixingSubgroup → c (g * s) = c g) ∧
      ∀ (g : Ω ≃ₐ[k] Ω) (s t : K.fixingSubgroup), (g⁻¹ * s * g : Ω ≃ₐ[k] Ω) = t → A.ρ g (c t) = c s)
    {VX : Type} [AddCommGroup VX] [Module (ZMod p) VX] (X : Representation (ZMod p) (Ω ≃ₐ[k] Ω) VX)
    (π : (↥K)ˣ → VX) (hπmul : ∀ a b, π (a * b) = π a + π b) (hπsurj : Function.Surjective π)
    (hπker : ∀ a : (↥K)ˣ, π a = 0 ↔ ∃ b : (↥K)ˣ, b ^ p = a)
    (hπG : ∀ (g : Ω ≃ₐ[k] Ω) (a b : (↥K)ˣ), g ((a : K) : Ω) = ((b : K) : Ω) → X g (π a) = π b) :
    finrank (ZMod p) W = finrank (ZMod p) ((A.dualTwist χ).ρ.linHom X).invariants := by sorry
