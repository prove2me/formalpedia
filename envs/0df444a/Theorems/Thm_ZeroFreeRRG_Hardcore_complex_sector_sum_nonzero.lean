-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_complex_sector_sum_nonzero
-- name    : ZeroFreeRRG.Hardcore.complex_sector_sum_nonzero
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:41:32.694198+00:00
-- url     : https://prove2.me/theorems/cfcdd566-7da8-4eb6-b42f-bd29a2374ca5
-- title:
--   A finite sum in a common complex sector is nonzero
-- statement:
--   Let $u$ be a unit complex number and $c>0$. If each complex summand $z_i$ in a finite set satisfies $\operatorname{Re}(\overline u z_i)\ge c|z_i|$, and at least one is nonzero, then $$\left|\sum_i z_i\right|\ge c\sum_i|z_i|>0.$$ This sector estimate is useful when summing restricted Potts partition functions.
-- source:
--   Auxiliary geometry for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem ZeroFreeRRG.Hardcore.complex_sector_sum_nonzero {ι : Type} (S : Finset ι) (z : ι → ℂ) (u : ℂ) (c : ℝ)
    (hu : ‖u‖ = 1) (hc : 0 < c)
    (hsector : ∀ i ∈ S, c * ‖z i‖ ≤ (star u * z i).re)
    (hne : ∃ i ∈ S, z i ≠ 0) :
    c * (∑ i ∈ S, ‖z i‖) ≤ ‖∑ i ∈ S, z i‖ ∧ (∑ i ∈ S, z i) ≠ 0 := by sorry
