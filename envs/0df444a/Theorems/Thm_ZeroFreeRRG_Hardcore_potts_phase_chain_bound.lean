-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_phase_chain_bound
-- name    : ZeroFreeRRG.Hardcore.potts_phase_chain_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:13:54.77828+00:00
-- url     : https://prove2.me/theorems/ff54afe5-be71-4271-b00d-c74b16b13f2c
-- title:
--   Phase coherence after boundedly many coefficient replacements
-- statement:
--   Consider at most $d$ successive replacements of coefficients on the segment from $1$ to $\beta$. If each original sum is sector-controlled with factor $7/8$ and the first sum is nonzero, then every successive sum is nonzero and the normalized endpoint phases differ by less than $1/2$, provided $d\ge3$ and $|\beta-1|<0.35/d$.
-- source:
--   Auxiliary phase estimate for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.potts_phase_chain_bound {ι : Type} (S : Finset ι) (d n : ℕ) (hd : 3 ≤ d) (hn : n ≤ d)
    (β : ℂ) (hβ : ‖β-1‖ < 0.35/(d:ℝ))
    (f : ℕ → ℂ) (z a b : ℕ → ι → ℂ) (hfirst : f 0 ≠ 0)
    (ha : ∀ k < n, ∀ i ∈ S, ∃ t : ℝ, t ∈ Icc 0 1 ∧ a k i = 1+(t:ℂ)*(β-1))
    (hb : ∀ k < n, ∀ i ∈ S, ∃ t : ℝ, t ∈ Icc 0 1 ∧ b k i = 1+(t:ℂ)*(β-1))
    (hsector : ∀ k < n, (7/8:ℝ)*(∑ i ∈ S, ‖z k i‖) ≤ ‖∑ i ∈ S, z k i‖)
    (hold : ∀ k < n, f k = ∑ i ∈ S, z k i)
    (hnew : ∀ k < n, f (k+1) = ∑ i ∈ S, (b k i/a k i)*z k i) :
    f n ≠ 0 ∧ ‖f 0/(‖f 0‖:ℂ)-f n/(‖f n‖:ℂ)‖ < 1/2 := by sorry
