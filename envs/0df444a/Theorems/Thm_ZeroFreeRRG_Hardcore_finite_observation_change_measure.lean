-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_finite_observation_change_measure
-- name    : ZeroFreeRRG.Hardcore.finite_observation_change_measure
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:14:07.049576+00:00
-- url     : https://prove2.me/theorems/da590865-aafc-4006-b182-5c5dcbf0ecfd
-- title:
--   Finite revealed-pattern change of measure
-- statement:
--   Let a finite observation map send full configurations to revealed patterns. Suppose the product of the two observed-pattern masses under a weight $p$ is at most $L$ times the corresponding product under a nonnegative reference weight $q$ on a revealed event and a good-density event. Then the full-configuration pair weight of the intersection of those events is at most $L$ times the reference revealed-event weight. The proof groups both configurations by their observed patterns.
-- source:
--   Auxiliary revealed-pattern change of measure for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, pp. 39–40, proof of Lemma 5.6.

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.finite_observation_change_measure {X Y : Type} [Fintype X] [Fintype Y]
    (obs : X → Y) (p : X → ℝ) (q : Y → ℝ) (H Good : Y → Y → Prop) (L : ℝ)
    (hL : 0 ≤ L) (hq : ∀ y, 0 ≤ q y)
    (hdensity : ∀ y y', H y y' → Good y y' →
      (∑ x ∈ Finset.univ.filter (fun x => obs x = y), p x) *
      (∑ x ∈ Finset.univ.filter (fun x => obs x = y'), p x) ≤ L * (q y * q y')) :
    (∑ x, ∑ x', if H (obs x) (obs x') ∧ Good (obs x) (obs x') then p x*p x' else 0) ≤
      L * ∑ y, ∑ y', if H y y' then q y*q y' else 0 := by sorry
