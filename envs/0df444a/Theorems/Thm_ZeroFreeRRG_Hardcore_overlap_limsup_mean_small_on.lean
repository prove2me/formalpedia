-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_limsup_mean_small_on
-- name    : ZeroFreeRRG.Hardcore.overlap_limsup_mean_small_on
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:40:11.257432+00:00
-- url     : https://prove2.me/theorems/05de23e1-8f37-45f4-9db3-5597af9db58a
-- title:
--   Likelihood limsup bound with continuity on the compact domain
-- statement:
--   Let $K$ be compact and $f,g$ be continuous on $K$, with $f\le0$, a unique zero $x_0$, and $g(x_0)=0$. If for each $0<s<1$ the limsup of $E(s,n)$ along admissible indices is at most $f(x_s)+sg(x_s)$ for some $x_s\in K$, then for every $\varepsilon>0$ some $0<s<1$ satisfies $E(s,n)\le\varepsilon s$ for all sufficiently large admissible $n$. This is the limsup-to-small-mean step for equation (29), requiring continuity only on the compact cavity-law domain.
-- source:
--   Auxiliary step in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, Lemma 5.6 and equation (29).

import Mathlib
set_option autoImplicit false
open Set Filter

theorem ZeroFreeRRG.Hardcore.overlap_limsup_mean_small_on {α : Type} [TopologicalSpace α] (K : Set α) (hK : IsCompact K)
    (f g : α → ℝ) (hf : ContinuousOn f K) (hg : ContinuousOn g K) (x₀ : α) (hx₀ : x₀ ∈ K)
    (hfnonpos : ∀ x ∈ K, f x ≤ 0) (hfzero : f x₀ = 0)
    (hunique : ∀ x ∈ K, f x = 0 → x = x₀) (hgzero : g x₀ = 0)
    (E : ℝ → ℕ → ℝ) (admissible : Set ℕ)
    (hlimsup : ∀ s : ℝ, 0 < s → s < 1 → ∃ x ∈ K,
      limsup (fun n => (E s n : EReal)) (atTop ⊓ 𝓟 admissible) ≤ (f x + s*g x : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      ∃ N : ℕ, ∀ n ≥ N, n ∈ admissible → E s n ≤ ε*s := by sorry
