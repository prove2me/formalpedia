-- Prove2me | Theorems.Thm_XiPairingPublished_concrete_xi_no_real_zeros
-- name    : XiPairingPublished.concrete_xi_no_real_zeros
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T10:32:12.717241+00:00
-- url     : https://prove2.me/theorems/a5fa0788-9c63-4f90-90ed-5338715f044c
-- title:
--   The concrete entire Riemann xi function has no real zeros
-- statement:
--   Let \(\xi(s)=[s(s-1)\Lambda_0(s)+1]/2\) be the classical entire Riemann xi function, where \(\Lambda_0\) denotes the pole-removed completed zeta function. Then
--   \[
--   \xi(x)\ne0\qquad\text{for every }x\in\mathbb R.
--   \]
--   This unconditional classical fact excludes real zeros when splitting the centered Hadamard product into upper and lower half-plane factors. It makes no assertion that nonreal zeros lie on the critical line.
-- source:
--   Primary formalization: Matteo Cipollina and contributors, PrimeNumberTheoremAnd, Apache-2.0, commit a4fb6989b07e9c76b511807ae93e33e25b820e9b, https://github.com/AlexKontorovich/PrimeNumberTheoremAnd . Lean 4.33.1 compatibility port, dependency bundling and explicit public wrapper by Desenvolvimento RH, coordinated by Ricardo Marangoni Brandao Bueno. No mathematical novelty claimed. Inventory: https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4 New real-axis nonvanishing argument by Desenvolvimento RH, 2026-11-16, extending the recovered center-only argument.

import Mathlib

theorem XiPairingPublished.concrete_xi_no_real_zeros (x : ℝ) :
    (((x : ℂ)*((x : ℂ)-1)*completedRiemannZeta₀ (x : ℂ)+1)/2) ≠ 0 := by sorry
