-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_unit_chord_sum_nonzero
-- name    : ZeroFreeRRG.Hardcore.unit_chord_sum_nonzero
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:52:37.467024+00:00
-- url     : https://prove2.me/theorems/6b526320-1131-4063-8c55-157708bfef7d
-- title:
--   Nonvanishing sum of complex numbers with nearby phases
-- statement:
--   Suppose a nonempty finite family of nonzero complex numbers has normalized phases within distance $1/2$ of a common unit complex number. Then the norm of their sum is at least $7/8$ of the sum of their norms, so the sum is nonzero.
-- source:
--   Auxiliary complex geometry for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem ZeroFreeRRG.Hardcore.unit_chord_sum_nonzero {ι : Type} (S : Finset ι) (z : ι → ℂ) (u : ℂ)
    (hu : ‖u‖ = 1) (hS : S.Nonempty)
    (hn : ∀ i ∈ S, z i ≠ 0)
    (hclose : ∀ i ∈ S, ‖u-z i/(‖z i‖:ℂ)‖ ≤ 1/2) :
    ((7:ℝ)/8) * (∑ i ∈ S, ‖z i‖) ≤ ‖∑ i ∈ S, z i‖ ∧ (∑ i ∈ S, z i) ≠ 0 := by sorry
