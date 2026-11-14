-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_change_of_measure
-- name    : ZeroFreeRRG.Hardcore.overlap_change_of_measure
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:33:31.366199+00:00
-- url     : https://prove2.me/theorems/b2f2bdf1-88e9-41d8-a4ec-6c48d95ae180
-- title:
--   Finite change of measure for overlap deviations
-- statement:
--   Let $p,q$ be nonnegative weights on a finite space, let $D$ be an overlap-deviation event, $H$ a revealed-deviation event, and $G$ a good density event. Suppose $p(x)\le Lq(x)$ on $H\cap G$, the $p$-weight of $D\cap H^c$ is at most $A$, the $q$-weight of $H$ is at most $B$, and the $p$-weight of $G^c$ is at most $C$. Then the $p$-weight of $D$ is at most $A+LB+C$. This is the finite change-of-measure decomposition in the proof of the exponential overlap bound.
-- source:
--   Auxiliary decomposition for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, pp. 39–40, proof of Lemma 5.6.

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.overlap_change_of_measure {Ω : Type} [Fintype Ω] (p q : Ω → ℝ) (D H Good : Ω → Prop)
    (L A B C : ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (hL : 0 ≤ L)
    (hdens : ∀ x, H x → Good x → p x ≤ L * q x)
    (hmiss : (∑ x, if D x ∧ ¬ H x then p x else 0) ≤ A)
    (hreference : (∑ x, if H x then q x else 0) ≤ B)
    (htail : (∑ x, if ¬ Good x then p x else 0) ≤ C) :
    (∑ x, if D x then p x else 0) ≤ A + L * B + C := by sorry
