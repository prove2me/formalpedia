-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_unique_maximum_small_perturbation
-- name    : ZeroFreeRRG.Hardcore.unique_maximum_small_perturbation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:35:59.056957+00:00
-- url     : https://prove2.me/theorems/007e7c55-3587-402e-892d-e5359c36a142
-- title:
--   Uniform small perturbation at a unique compact maximizer
-- statement:
--   Let $K$ be a compact set and $f,g$ be continuous real functions. Suppose $f\le0$ on $K$, $f$ vanishes at exactly one point $x_0\in K$, and $g(x_0)=0$. Then for every $\varepsilon>0$ there is $s_0>0$ such that $$f(x)+s g(x)\le\varepsilon s$$ uniformly over $x\in K$ and $0<s<s_0$. This is the compactness and unique-maximizer step behind the $o(s)$ estimate used in Lemma 5.6.
-- source:
--   Auxiliary analytic step in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6 using equation (29).

import Mathlib
set_option autoImplicit false
open Set

theorem ZeroFreeRRG.Hardcore.unique_maximum_small_perturbation {α : Type} [TopologicalSpace α] (K : Set α) (hK : IsCompact K)
    (f g : α → ℝ) (hf : Continuous f) (hg : Continuous g) (x₀ : α) (hx₀ : x₀ ∈ K)
    (hfnonpos : ∀ x ∈ K, f x ≤ 0) (_hfzero : f x₀ = 0)
    (hunique : ∀ x ∈ K, f x = 0 → x = x₀) (hgzero : g x₀ = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ s₀ : ℝ, 0 < s₀ ∧
      ∀ s : ℝ, 0 < s → s < s₀ → ∀ x ∈ K, f x + s * g x ≤ ε * s := by sorry
