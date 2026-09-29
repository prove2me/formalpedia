-- Prove2me | Theorems.Thm_groupCohomology_exists_continuousH2Sr_trivial_tensor_linearEquiv
-- name    : groupCohomology.exists_continuousH2Sr_trivial_tensor_linearEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/e55202c3-b8fb-5ec9-845d-c9dfd23a6f78
-- title:
--   Trivial finite-dimensional coefficients factor out of H²_S
-- statement:
--   Let $k$ be a field, $G$ a group, $r : G \to \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ a group homomorphism into the $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$, $S$ a finite set of rational primes, $V$ a finite-dimensional $k$-vector space and $X$ a representation of $G$ over $k$. Here, for a representation $M$, $\mathtt{continuousH2Sr}\ r\ S\ M$ is the quotient of the submodule `levelCocyclesSr₂ r S M` of functions $G \times G \to M$ by the preimage of `levelCoboundariesSr₂ r S M` under its inclusion, with quotient map `continuousH2Srπ r S M`, and for a morphism $\varphi$ of representations `continuousH2SrMapHom S r φ` is the induced $k$-linear map on these quotients. The assertion is that there exists a $k$-linear isomorphism $\Theta$ from $\mathtt{continuousH2Sr}\ r\ S\ (\mathrm{triv}(V) \otimes X)$ onto $V \otimes_k \mathtt{continuousH2Sr}\ r\ S\ X$, where $\mathrm{triv}(V)$ carries the trivial $G$-action, with two properties. First, for every $v \in V$, every $z$ in `levelCocyclesSr₂ r S X` and every $w$ in `levelCocyclesSr₂ r S (Rep.trivial k G V ⊗ X)` whose value at each $(g,h) \in G \times G$ equals $v \otimes z(g,h)$, one has $\Theta([w]) = v \otimes [z]$. Second, $\Theta$ is natural in both factors: for every $k$-linear $\varphi : V \to V$, every endomorphism $\psi$ of $X$ in $\mathrm{Rep}_k G$ and every endomorphism $e$ of $\mathrm{triv}(V) \otimes X$ in $\mathrm{Rep}_k G$ acting on pure tensors by $v \otimes x \mapsto \varphi(v) \otimes \psi(x)$, the composite of `continuousH2SrMapHom S r e` followed by $\Theta$ equals the composite of $\Theta$ followed by $\varphi \otimes \mathtt{continuousH2SrMapHom}\ S\ r\ \psi$.
--
--   This is the statement that trivial finite-dimensional coefficients pull out of the continuous $S$-level second cohomology, $H^2_S(r, V \otimes X) \cong V \otimes H^2_S(r, X)$, together with naturality in both the linear endomorphism of $V$ and the representation endomorphism of $X$; the naturality clause for non-identity $\varphi$ is what allows averaging idempotents on tensor products to be transported through $H^2_S$. It is used in the construction of the twisting isomorphism [`groupCohomology.nonempty_continuousH2Sr_twist_linearEquiv_invariants_cyclotomicQuotientH2Rep_tensor`](thm.html#groupCohomology.nonempty_continuousH2Sr_twist_linearEquiv_invariants_cyclotomicQuotientH2Rep_tensor).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_continuousH2Sr_trivial_tensor_linearEquiv.lean

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
open scoped TensorProduct

theorem groupCohomology.exists_continuousH2Sr_trivial_tensor_linearEquiv
    {k : Type} [Field k] {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
    (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (X : Rep.{0} k G) :
    ∃ Θ : continuousH2Sr r S (Rep.trivial k G V ⊗ X) ≃ₗ[k] V ⊗[k] continuousH2Sr r S X,
      (∀ (v : V) (z : ↥(levelCocyclesSr₂ r S X)) (w : ↥(levelCocyclesSr₂ r S (Rep.trivial k G V ⊗ X))),
        (∀ st, (w : G × G → (Rep.trivial k G V ⊗ X : Rep.{0} k G)) st = v ⊗ₜ[k] (z : G × G → X) st) →
          Θ (continuousH2Srπ r S (Rep.trivial k G V ⊗ X) w) = v ⊗ₜ[k] continuousH2Srπ r S X z) ∧
      ∀ (φ : V →ₗ[k] V) (ψ : X ⟶ X) (e : (Rep.trivial k G V ⊗ X : Rep.{0} k G) ⟶ (Rep.trivial k G V ⊗ X : Rep.{0} k G)),
        (∀ (v : V) (x : X), e.hom (v ⊗ₜ[k] x) = φ v ⊗ₜ[k] ψ.hom x) →
          Θ.toLinearMap ∘ₗ continuousH2SrMapHom S r e = TensorProduct.map φ (continuousH2SrMapHom S r ψ) ∘ₗ Θ.toLinearMap := by sorry
