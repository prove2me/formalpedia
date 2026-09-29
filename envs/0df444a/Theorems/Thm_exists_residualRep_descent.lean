-- Prove2me | Theorems.Thm_exists_residualRep_descent
-- name    : exists_residualRep_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/cb75ba25-94a7-5d6f-92c2-6e0d2ea0ab47
-- title:
--   Descent of a residual representation to Gal(L₀/ℚ)
-- statement:
--   Let $k$ be a field and let $\bar\rho$ be a residual Galois representation over $k$: a $k$-vector space $V$ with $\dim_k V = 2$, a monoid homomorphism $\bar\rho\colon \operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}}) \to \operatorname{End}_k V$ (where $\overline{\mathbb{Q}}$ is `AlgebraicClosure ℚ`), together with the datum of some intermediate field $L \subseteq \overline{\mathbb{Q}}$, finite over $\mathbb{Q}$, such that $\bar\rho(\sigma) = 1$ whenever $\sigma$ fixes $L$ pointwise. Let $L_0 \subseteq \overline{\mathbb{Q}}$ be an intermediate field which is finite-dimensional over $\mathbb{Q}$, a number field, and Galois over $\mathbb{Q}$, and assume $\bar\rho(\sigma) = 1$ for every $\sigma \in \operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ fixing $L_0$ pointwise. Let $b$ be a basis of $V$ indexed by `Fin 2`. Then there exists a monoid homomorphism $\rho_{\mathrm{mat}}$ from $\operatorname{Aut}_{\mathbb{Q}}(L_0)$ to the multiplicative monoid of $2 \times 2$ matrices over $k$ such that for every $\sigma \in \operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$, the value of $\rho_{\mathrm{mat}}$ at the restriction of $\sigma$ to $L_0$ equals the matrix of $\bar\rho(\sigma)$ in the basis $b$. The descent depends on $b$; the proof uses only the normality of $L_0$ over $\mathbb{Q}$, not the finiteness or number-field hypotheses, nor the finite level attached to $\bar\rho$.
--
--   This is the standard descent step of Galois theory: a homomorphism out of $\operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ that is trivial on the automorphisms fixing a normal subextension $L_0$ factors through the restriction map onto $\operatorname{Aut}_{\mathbb{Q}}(L_0)$. It converts a residual Galois representation into a matrix representation of a finite Galois group, the form in which the Taylor–Wiles prime arguments operate; it is used in the production of Taylor–Wiles primes avoiding a given set for absolutely irreducible residual representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_residualRep_descent.lean

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_TaylorWiles_Primes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem exists_residualRep_descent {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L₀]
    [NumberField L₀] [IsGalois ℚ L₀]
    (hker : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (∀ x ∈ L₀, σ x = x) → ρbar.ρ σ = 1)
    (b : Module.Basis (Fin 2) k ρbar.V) :
    ∃ ρmat : TaylorWiles.ResidualRep (↥L₀) k,
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        ρmat (AlgEquiv.restrictNormalHom (↥L₀) σ)
          = LinearMap.toMatrix b b (ρbar.ρ σ) := by sorry
