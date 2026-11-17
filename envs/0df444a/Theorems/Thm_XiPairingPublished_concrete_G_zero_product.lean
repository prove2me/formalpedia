-- Prove2me | Theorems.Thm_XiPairingPublished_concrete_G_zero_product
-- name    : XiPairingPublished.concrete_G_zero_product
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T11:28:10.557117+00:00
-- url     : https://prove2.me/theorems/18163244-d1ff-4df7-9355-4de81fb6a976
-- title:
--   Normalized xi product over its original upper zeros
-- statement:
--   Let xi be the completed Riemann xi function, and let rho run through all its zeros in the upper half-plane, counted with analytic multiplicity. Define G(x)=Re xi(1/2+sqrt(x)). For every real x≥0, the product below converges and
--   $$\frac{G(x)}{G(0)}=\prod_{\Im\rho>0}\left(1+\frac{x}{-(\rho-1/2)^2}\right).$$
--   This is an unconditional classical product identity; it assumes neither RH nor numerical zero bounds.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4. Analytic dependencies: Matteo Cipollina and contributors, PrimeNumberTheoremAnd, Apache-2.0, commit a4fb6989b07e9c76b511807ae93e33e25b820e9b. Classical mathematics; no novelty claim.
--   Additional original-coordinate translation and real-valuedness by Desenvolvimento RH; xi_original_product.lean.

import Mathlib
open scoped BigOperators

theorem XiPairingPublished.concrete_G_zero_product :
    let f : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let Z : Type := (z : {z : ℂ // f z = 0 ∧ 0 < z.im}) × Fin (analyticOrderNatAt f z.val)
    let G : ℝ → ℝ := fun x => (f (1/2+(Real.sqrt x : ℂ))).re
    ∀ x : ℝ, 0 ≤ x →
      Multipliable (fun p : Z => 1+(x : ℂ)/(-(p.1.val-1/2)^2)) ∧
      ((G x/G 0 : ℝ) : ℂ) = ∏' p : Z, (1+(x : ℂ)/(-(p.1.val-1/2)^2))  := by sorry
