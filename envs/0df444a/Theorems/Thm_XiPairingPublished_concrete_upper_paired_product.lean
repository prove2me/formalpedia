-- Prove2me | Theorems.Thm_XiPairingPublished_concrete_upper_paired_product
-- name    : XiPairingPublished.concrete_upper_paired_product
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T11:09:12.475081+00:00
-- url     : https://prove2.me/theorems/c356a1b9-33f8-49c2-a388-e8c03f856943
-- title:
--   The convergent normalized Hadamard product over upper zeros of concrete Riemann xi
-- statement:
--   Let F(w)=xi(1/2+w). Let U consist of the upper zeros a of F, each repeated according to its exact analytic multiplicity. For every complex w the product below converges, and
--   \[
--   \frac{\xi(1/2+w)}{\xi(1/2)}=\prod_{a\in U}\left(1+\frac{w^2}{-a^2}\right).
--   \]
--   The theorem is unconditional for the concrete entire xi. Neither RH nor simple zeros nor a product identity is assumed. No undetermined exponential factor remains. The upper index uses centered coordinates and analytic order.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4. Analytic dependencies: Matteo Cipollina and contributors, PrimeNumberTheoremAnd, Apache-2.0, commit a4fb6989b07e9c76b511807ae93e33e25b820e9b. Classical mathematics; no novelty claim.

import Mathlib
open scoped BigOperators

theorem XiPairingPublished.concrete_upper_paired_product :
    let f : ℂ → ℂ := fun s => (s*(s-1)*completedRiemannZeta₀ s+1)/2
    let F : ℂ → ℂ := fun z => f (z+1/2)
    let U : Type := (z : {z : ℂ // 0 < z.im}) × Fin (analyticOrderNatAt F z.val)
    ∀ w : ℂ, Multipliable (fun p : U => 1+w^2/(-p.1.val^2)) ∧
      F w/F 0 = ∏' p : U, (1+w^2/(-p.1.val^2)) := by sorry
