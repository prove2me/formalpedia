-- Prove2me | Theorems.Thm_XiQuantitativePublished_concrete_upper_zero_anchor
-- name    : XiQuantitativePublished.concrete_upper_zero_anchor
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T12:33:18.454836+00:00
-- url     : https://prove2.me/theorems/56caf034-0baa-4abf-aa91-0541f7ff3c01
-- title:
--   A concrete upper xi zero occurrence below height one hundred
-- statement:
--   For the entire Riemann xi function ξ(s)=(1+s(s−1)Λ₀(s))/2, indexed over all upper-half-plane zeros with their analytic multiplicities, there exists an occurrence on Re(s)=1/2 whose ordinate lies strictly between 14.13 and 14.14, and in particular is at most 100. No RH, simplicity or prior existence hypothesis is assumed.
-- source:
--   Adapted from teal-sea/zeta-lab, MIT license, commit a401821c9608526425f3d4cf7ff8e59bc37e1c79, hunts/hardy_first_zero and lean/ZetaLean/{HardyZ,Rigor,IntervalExp,IntervalCExp}.lean. https://github.com/teal-sea/zeta-lab. Mathlib arctangent bound backport from commit 065356127b1dc0016f66b7283ce0ce2c4055aa55 (Apache-2.0). Lean4.33.1 port and Branch integration: Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. No novelty claim.

import Mathlib

theorem XiQuantitativePublished.concrete_upper_zero_anchor :
    let f : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let Z : Type := (s : {s : ℂ // f s = 0 ∧ 0 < s.im}) × Fin (analyticOrderNatAt f s.val)
    ∃ i : Z, i.1.val.re = 1/2 ∧ 1413/100 < i.1.val.im ∧
      i.1.val.im < 707/50 ∧ i.1.val.im ≤ 100 := by sorry
