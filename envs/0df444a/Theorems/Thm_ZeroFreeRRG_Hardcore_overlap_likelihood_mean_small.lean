-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_likelihood_mean_small
-- name    : ZeroFreeRRG.Hardcore.overlap_likelihood_mean_small
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:37:23.26831+00:00
-- url     : https://prove2.me/theorems/dddd866e-967f-4bb5-954a-4ca7ac314c56
-- title:
--   Small normalized likelihood mean from a compact variational envelope
-- statement:
--   Let $K$ be compact and let continuous $f,g$ have $f\le0$ on $K$, unique zero $x_0$, and $g(x_0)=0$. Suppose that for each $0<s<1$ and $\delta>0$, the sequence $E(s,n)$ is eventually bounded above by $\sup_{x\in K}(f(x)+sg(x))+\delta$. Then for every $\varepsilon>0$ some $0<s<1$ satisfies $E(s,n)\le\varepsilon s$ for all sufficiently large $n$. This is the abstract passage from the variational upper bound (29) to the small expected reveal log-likelihood used in Lemma 5.6.
-- source:
--   Auxiliary step in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, Lemma 5.6 and equation (29).

import Mathlib
set_option autoImplicit false
open Set

theorem ZeroFreeRRG.Hardcore.overlap_likelihood_mean_small {α : Type} [TopologicalSpace α] (K : Set α) (hK : IsCompact K)
    (f g : α → ℝ) (hf : Continuous f) (hg : Continuous g) (x₀ : α) (hx₀ : x₀ ∈ K)
    (hfnonpos : ∀ x ∈ K, f x ≤ 0) (hfzero : f x₀ = 0)
    (hunique : ∀ x ∈ K, f x = 0 → x = x₀) (hgzero : g x₀ = 0)
    (E : ℝ → ℕ → ℝ)
    (hbound : ∀ s : ℝ, 0 < s → s < 1 → ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∃ x ∈ K, E s n ≤ f x + s*g x + δ) :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      ∃ N : ℕ, ∀ n ≥ N, E s n ≤ ε*s := by sorry
