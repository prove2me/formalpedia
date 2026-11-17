-- Prove2me | Theorems.Thm_XiPairingPublished_concrete_divisor_reindex
-- name    : XiPairingPublished.concrete_divisor_reindex
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T11:03:37.82113+00:00
-- url     : https://prove2.me/theorems/f06d7e4a-9358-4b5e-9bcf-eac69b3c60de
-- title:
--   Multiplicity-preserving reindexing of the concrete xi divisor product
-- statement:
--   Let F(z)=xi(1/2+z), let U index its upper zeros with analytic multiplicities, and let D index all nonzero zeros by the positive part of the analytic divisor. There is a bijection e:U⊔U→D preserving multiplicity labels and sending the two copies of a to a and -a, respectively. For every complex w, the genus-one product over D equals the product reindexed by e. The theorem is unconditional for the explicit Riemann xi. This reindexing does not by itself assert convergence of either half-product or identify the paired product with the derivative-defined Q.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4. Analytic dependencies: Matteo Cipollina and contributors, PrimeNumberTheoremAnd, Apache-2.0, commit a4fb6989b07e9c76b511807ae93e33e25b820e9b. Classical mathematics; no novelty claim.

import Mathlib
open scoped BigOperators

theorem XiPairingPublished.concrete_divisor_reindex :
    let f : ℂ → ℂ := fun s => (s*(s-1)*completedRiemannZeta₀ s+1)/2
    let F : ℂ → ℂ := fun z => f (z+1/2)
    let U : Type := (z : {z : ℂ // 0 < z.im}) × Fin (analyticOrderNatAt F z.val)
    let D : Type := {p : (z : ℂ) × Fin ((MeromorphicOn.divisor F Set.univ z).toNat) // p.1 ≠ 0}
    ∃ e : U ⊕ U ≃ D,
      (∀ p, (e (Sum.inl p)).val.1 = p.1.val ∧ (e (Sum.inl p)).val.2.val = p.2.val) ∧
      (∀ p, (e (Sum.inr p)).val.1 = -p.1.val ∧ (e (Sum.inr p)).val.2.val = p.2.val) ∧
      (∀ w : ℂ, (∏' d : D, ((1-w/d.val.1)*Complex.exp (w/d.val.1))) =
        ∏' p : U ⊕ U, ((1-w/(e p).val.1)*Complex.exp (w/(e p).val.1))) := by sorry
