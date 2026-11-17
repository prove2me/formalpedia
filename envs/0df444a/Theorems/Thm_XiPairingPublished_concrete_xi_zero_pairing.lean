-- Prove2me | Theorems.Thm_XiPairingPublished_concrete_xi_zero_pairing
-- name    : XiPairingPublished.concrete_xi_zero_pairing
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T10:37:01.87037+00:00
-- url     : https://prove2.me/theorems/c08070e3-c067-4bb1-926a-5451a956ca91
-- title:
--   An exact upper-lower pairing of the centered Riemann xi zero indices
-- statement:
--   Let \(F(z)=\xi(1/2+z)\), and write \(m(z)\) for its analytic zero multiplicity, with \(m(z)=0\) at a nonzero value. Define
--   \[
--   A=\{(z,j):z\in\mathbb C,\ 0\le j<m(z)\},\quad
--   U=\{(z,j)\in A:\Im z>0\}.
--   \]
--   There is a bijection \(e:U\sqcup U\to A\) such that \(e\) sends the first copy of \((z,j)\) to \((z,j)\) and the second copy to \((-z,j)\). Thus the pairing preserves each multiplicity label exactly. The theorem is unconditional for the explicit entire Riemann xi function. It does not place the nonreal zeros on the imaginary axis and does not by itself reindex an infinite product.
-- source:
--   Primary formalization: Matteo Cipollina and contributors, PrimeNumberTheoremAnd, Apache-2.0, commit a4fb6989b07e9c76b511807ae93e33e25b820e9b, https://github.com/AlexKontorovich/PrimeNumberTheoremAnd . Lean 4.33.1 compatibility port, dependency bundling and explicit public wrapper by Desenvolvimento RH, coordinated by Ricardo Marangoni Brandao Bueno. No mathematical novelty claimed. Inventory: https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4 New real-axis nonvanishing argument by Desenvolvimento RH, 2026-11-16, extending the recovered center-only argument.

import Mathlib

theorem XiPairingPublished.concrete_xi_zero_pairing :
    let f : ℂ → ℂ := fun s => (s*(s-1)*completedRiemannZeta₀ s+1)/2
    let F : ℂ → ℂ := fun z => f (z+1/2)
    let U : Type := (z : {z : ℂ // 0 < z.im}) × Fin (analyticOrderNatAt F z.val)
    let A : Type := (z : ℂ) × Fin (analyticOrderNatAt F z)
    ∃ e : U ⊕ U ≃ A,
      (∀ p, (e (Sum.inl p)).1 = p.1.val ∧ (e (Sum.inl p)).2.val = p.2.val) ∧
      (∀ p, (e (Sum.inr p)).1 = -p.1.val ∧ (e (Sum.inr p)).2.val = p.2.val) := by sorry
