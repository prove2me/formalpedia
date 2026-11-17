-- Prove2me | Theorems.Thm_XiHadamardPortPublished_concrete_xi_global_hadamard
-- name    : XiHadamardPortPublished.concrete_xi_global_hadamard
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T10:05:39.26848+00:00
-- url     : https://prove2.me/theorems/d5772aee-b100-496f-bd09-51e308324c44
-- title:
--   Global Hadamard factorization and inverse-square zero summability for the concrete Riemann xi
-- statement:
--   Let xi(s)=[s(s-1) completedRiemannZeta₀(s)+1]/2 be the concrete entire Riemann xi function. Index every nonzero zero by its divisor multiplicity, and denote its position by rho_i. Then sum_i |rho_i|^(-2) converges and there exists a complex polynomial P of degree at most one such that, for every complex z, xi(z)=exp(P(z)) product_i [(1-z/rho_i) exp(z/rho_i)]. The entire-function growth estimate and convergence are proved within the supplied proof, not assumed. This is the classical origin-centered genus-one product with its exponential factor retained; it is not yet the paired, normalized product centered at 1/2 needed by the project's Q tower. This theorem does not prove RH.
-- source:
--   Primary formalization: Matteo Cipollina and contributors, PrimeNumberTheoremAnd, Apache-2.0, commit a4fb6989b07e9c76b511807ae93e33e25b820e9b, https://github.com/AlexKontorovich/PrimeNumberTheoremAnd . Lean 4.33.1 compatibility port, dependency bundling and explicit public wrapper by Desenvolvimento RH, coordinated by Ricardo Marangoni Brandao Bueno. No mathematical novelty claimed. Inventory: https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4

import Mathlib
open scoped BigOperators

theorem XiHadamardPortPublished.concrete_xi_global_hadamard :
    let f : ℂ → ℂ := fun s => (s*(s-1)*completedRiemannZeta₀ s+1)/2
    let I : Type := {p : ((z : ℂ) × Fin ((MeromorphicOn.divisor f Set.univ z).toNat)) // p.1 ≠ 0}
    let rho : I → ℂ := fun p => p.val.1
    Summable (fun i => ‖rho i‖⁻¹ ^ (2 : ℕ)) ∧
    ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧ ∀ z : ℂ,
      f z = Complex.exp (Polynomial.eval z P) *
        ∏' i : I, ((1-z/rho i)*Complex.exp (z/rho i)) := by sorry
