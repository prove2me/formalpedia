-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_weighted_sector_perturbation
-- name    : ZeroFreeRRG.Hardcore.weighted_sector_perturbation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:09:47.025924+00:00
-- url     : https://prove2.me/theorems/1d16d259-4bdf-4b91-8ff4-900697a49801
-- title:
--   Perturbing coefficients of a sector-controlled sum
-- statement:
--   If the coefficients $a_i$ have modulus at least $1-\delta$, their replacements differ by at most $\delta$, and $|\sum z_i|\ge\tau\sum|z_i|$, then replacing $z_i$ by $(b_i/a_i)z_i$ changes the sum by at most $\delta|\sum z_i|/(\tau(1-\delta))$.
-- source:
--   Auxiliary step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.weighted_sector_perturbation {ι : Type} (S : Finset ι) (z a b : ι → ℂ) (δ τ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hτ : 0 < τ)
    (ha : ∀ i ∈ S, 1-δ ≤ ‖a i‖)
    (hab : ∀ i ∈ S, ‖b i-a i‖ ≤ δ)
    (hsector : τ*(∑ i ∈ S, ‖z i‖) ≤ ‖∑ i ∈ S, z i‖) :
    ‖(∑ i ∈ S, (b i/a i)*z i) - ∑ i ∈ S, z i‖ ≤
      (δ/(τ*(1-δ))) * ‖∑ i ∈ S, z i‖ := by sorry
