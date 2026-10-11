-- Prove2me | Definitions.Def_palis_vector_field
-- name    : palis_vector_field
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T02:52:57.58179+00:00
-- url     : https://prove2.me/theorems/bbbe55dc-8fde-4e8b-bd6b-56982c0b2c4a
-- title:
--   $C^r$ vector fields, chart representatives and flows
-- statement:
--   Let $M$ be a smooth manifold modelled on $\mathbb R^n$ and $X$ a vector field on $M$, i.e. $X(x)\in T_xM$ for each $x$.
--
--   1. $X$ is **of class $C^r$** if the section $x\mapsto (x,X(x))$ of the tangent bundle $TM$ is $C^r$.
--   2. For a chart $e$ of $M$, the **local representative** of $X$ is the map $X_e:\mathbb R^n\to\mathbb R^n$, $X_e(y)=De\big(e^{-1}(y)\big)\,X\big(e^{-1}(y)\big)$ (meaningful on the chart's image).
--   3. A map $\Phi:\mathbb R\times M\to M$ is a **(global) flow of $X$** if $\Phi_0(p)=p$ and $t\mapsto\Phi_t(p)$ is an integral curve of $X$, i.e. $\frac{d}{dt}\Phi_t(p)=X(\Phi_t(p))$ for all $t\in\mathbb R$, for every $p\in M$.
--
--   **Formalization Note** The derivative of the chart is Mathlib's `mfderiv`; integral curves are `IsMIntegralCurve`. $M$ carries a $C^\infty$ manifold structure `IsManifold (𝓡 n) ∞ M`.
-- source:
--   Open Problem Garden, "Jacob Palis Conjecture (Finitude of Attractors) (Dynamical Systems)", posted by Jailton Viana, April 24, 2013, https://www.openproblemgarden.org/op/jacob_palis_conjecture_finitude_of_attractors_dynamical_systems (Conjecture box and the Definition of attractor below it); bibliography: C. Bonatti, L. J. Diaz, M. Viana, Dynamics Beyond Uniform Hyperbolicity, Encyclopaedia of Mathematical Sciences 102, Springer, 2005.

import Mathlib

/-!
# `C^r` vector fields, their chart representatives, and their flows
-/

namespace PalisConjecture

open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- A vector field `X` on `M` is of class `C^r`: the section `x ↦ (x, X x)` of the tangent
bundle is `C^r`. -/
def IsCrVectorField (r : ℕ) (X : (x : M) → TangentSpace (𝓡 n) x) : Prop :=
  ContMDiff (𝓡 n) (𝓡 n).tangent r (fun x => (⟨x, X x⟩ : TangentBundle (𝓡 n) M))

/-- The local representative of a vector field `X` in a chart `e`: the map
`y ↦ D e (e⁻¹ y) (X (e⁻¹ y))` on `ℝⁿ` (meaningful for `y ∈ e.target`). -/
noncomputable def vfLocalRep (X : (x : M) → TangentSpace (𝓡 n) x)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun y => mfderiv (𝓡 n) (𝓡 n) e (e.symm y) (X (e.symm y))

/-- `Φ : ℝ → M → M` is the (global) flow of the vector field `X`: `Φ 0 = id` and every orbit
`t ↦ Φ t p` is an integral curve of `X`. -/
def IsFlowOf (X : (x : M) → TangentSpace (𝓡 n) x) (Φ : ℝ → M → M) : Prop :=
  ∀ p : M, Φ 0 p = p ∧ IsMIntegralCurve (fun t => Φ t p) X

end PalisConjecture


