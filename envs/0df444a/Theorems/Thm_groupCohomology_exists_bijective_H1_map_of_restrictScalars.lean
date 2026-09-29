-- Prove2me | Theorems.Thm_groupCohomology_exists_bijective_H1_map_of_restrictScalars
-- name    : groupCohomology.exists_bijective_H1_map_of_restrictScalars
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/8aa47cf1-2d77-5b25-beaf-165e076c1fa0
-- title:
--   H¹ under restriction of scalars of a representation
-- statement:
--   Let $k \subseteq K$ be fields with $K$ a $k$-algebra, let $G$ be a group, and let $V$ be an additive commutative group carrying both a $K$-module and a $k$-module structure, compatibly (a scalar tower $k$, $K$, $V$). Let $\rho$ be a $K$-linear representation of $G$ on $V$ and $\rho_0$ a $k$-linear representation of $G$ on $V$, and assume that the two actions agree: $\rho_0(g)v = \rho(g)v$ for all $g \in G$, $v \in V$. The assertion is the existence of a map $\Psi \colon H^1(\mathrm{Rep.of}\ \rho_0) \to H^1(\mathrm{Rep.of}\ \rho)$, semilinear with respect to the structure morphism $k \to K$, with three properties: $\Psi$ is bijective; whenever a $1$-cocycle $c_0$ for $\rho_0$ and a $1$-cocycle $c$ for $\rho$ are equal as functions $G \to V$, then $\Psi$ carries the class of $c_0$ to the class of $c$; and, when $K$ is finite-dimensional over $k$, for every $K$-submodule $X$ of $H^1(\mathrm{Rep.of}\ \rho)$ the preimage $\Psi^{-1}(X)$, viewed as a $k$-module, satisfies $\dim_k \Psi^{-1}(X) = \dim_k K \cdot \dim_K X$.
--
--   This is the standard observation that first group cohomology is insensitive to restriction of scalars: cocycles and coboundaries are defined by conditions not involving the scalars, so the $k$- and $K$-theories have literally the same $Z^1$ and $B^1$. It is used to transfer dimension counts for local and global Galois cohomology groups stated over a small coefficient field to representations over a larger one, being cited in the construction of submodules bounded by invariants under a unipotent inertia action and in the estimate of the space of dual-number classes at a set of Taylor–Wiles primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_bijective_H1_map_of_restrictScalars.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open groupCohomology

universe u

theorem groupCohomology.exists_bijective_H1_map_of_restrictScalars
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : Type u} [Group G]
    {V : Type u} [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    (ρ : Representation K G V) (ρ₀ : Representation k G V)
    (hρ : ∀ g v, ρ₀ g v = ρ g v) :
    ∃ Ψ : H1 (Rep.of ρ₀) →ₛₗ[algebraMap k K] H1 (Rep.of ρ),
      Function.Bijective Ψ ∧
      (∀ (c₀ : cocycles₁ (Rep.of ρ₀)) (c : cocycles₁ (Rep.of ρ)), (c₀ : G → V) = c →
        Ψ (H1π (Rep.of ρ₀) c₀) = H1π (Rep.of ρ) c) ∧
      (∀ [FiniteDimensional k K], ∀ X : Submodule K (H1 (Rep.of ρ)),
        Module.finrank k (X.comap Ψ) = Module.finrank k K * Module.finrank K X) := by sorry
