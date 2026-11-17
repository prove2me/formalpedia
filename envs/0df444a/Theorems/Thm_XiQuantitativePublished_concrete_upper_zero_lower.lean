-- Prove2me | Theorems.Thm_XiQuantitativePublished_concrete_upper_zero_lower
-- name    : XiQuantitativePublished.concrete_upper_zero_lower
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T12:23:40.388207+00:00
-- url     : https://prove2.me/theorems/17999532-6b5a-44b7-8ad3-563a28dcfb74
-- title:
--   Every upper xi zero occurrence has ordinate greater than three
-- statement:
--   Let ξ(s)=(1+s(s−1)Λ₀(s))/2 be the entire Riemann xi function, and index its upper-half-plane zeros with their analytic multiplicities. Every such occurrence has imaginary part strictly greater than 3, hence at least 2. This gives an unconditional lower ordinate bound for the concrete xi zero index.
-- source:
--   Adapted from teal-sea/zeta-lab, commit a401821c9608526425f3d4cf7ff8e59bc37e1c79, hunts/hardy_first_zero/lean/HardyFirstZero/EulerMaclaurin.lean and hunts/rh_height_lean/lean/RHHeight/LowHeight.lean. https://github.com/teal-sea/zeta-lab. Lean 4.33.1 port and Branch integration: Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4. No novelty claim.

import Mathlib

theorem XiQuantitativePublished.concrete_upper_zero_lower :
    let f : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let Z : Type := (s : {s : ℂ // f s = 0 ∧ 0 < s.im}) × Fin (analyticOrderNatAt f s.val)
    ∀ i : Z, 3 < i.1.val.im ∧ 2 ≤ i.1.val.im := by sorry
