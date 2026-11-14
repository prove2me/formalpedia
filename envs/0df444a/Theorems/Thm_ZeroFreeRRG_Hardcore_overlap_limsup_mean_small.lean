-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_limsup_mean_small
-- name    : ZeroFreeRRG.Hardcore.overlap_limsup_mean_small
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:38:17.019262+00:00
-- url     : https://prove2.me/theorems/b334c898-b078-4a1d-b773-21cb378ca9ce
-- title:
--   Small likelihood mean from the variational limsup bound
-- statement:
--   Let $K$ be compact and let continuous $f,g$ satisfy $f\le0$ on $K$, with a unique zero $x_0$, and $g(x_0)=0$. Suppose that for each $0<s<1$ there is an $x_s\in K$ such that the limsup along an admissible sequence satisfies $$\limsup_{n\to\infty} E(s,n)\le f(x_s)+s g(x_s).$$ Then for every $\varepsilon>0$ there is $0<s<1$ such that $E(s,n)\le\varepsilon s$ for all sufficiently large admissible $n$. This formalizes the analytic step from the limsup bound (29) to a small expected normalized reveal log-likelihood in Lemma 5.6.
-- source:
--   Auxiliary step in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, Lemma 5.6 and equation (29).

import Mathlib
set_option autoImplicit false
open Set Filter

theorem ZeroFreeRRG.Hardcore.overlap_limsup_mean_small {α : Type} [TopologicalSpace α] (K : Set α) (hK : IsCompact K)
    (f g : α → ℝ) (hf : Continuous f) (hg : Continuous g) (x₀ : α) (hx₀ : x₀ ∈ K)
    (hfnonpos : ∀ x ∈ K, f x ≤ 0) (hfzero : f x₀ = 0)
    (hunique : ∀ x ∈ K, f x = 0 → x = x₀) (hgzero : g x₀ = 0)
    (E : ℝ → ℕ → ℝ) (admissible : Set ℕ)
    (hlimsup : ∀ s : ℝ, 0 < s → s < 1 → ∃ x ∈ K,
      limsup (fun n => (E s n : EReal)) (atTop ⊓ 𝓟 admissible) ≤ (f x + s*g x : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      ∃ N : ℕ, ∀ n ≥ N, n ∈ admissible → E s n ≤ ε*s := by sorry
