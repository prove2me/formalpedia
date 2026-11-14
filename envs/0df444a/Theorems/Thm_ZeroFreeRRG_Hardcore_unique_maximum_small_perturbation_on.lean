-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_unique_maximum_small_perturbation_on
-- name    : ZeroFreeRRG.Hardcore.unique_maximum_small_perturbation_on
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:39:38.156303+00:00
-- url     : https://prove2.me/theorems/497d154e-964d-4faf-bb8c-8193c18b94db
-- title:
--   Small perturbations on a compact domain with a unique maximizer
-- statement:
--   Let $K$ be compact and let $f,g$ be continuous on $K$. Suppose $f\le0$ on $K$, with a unique zero $x_0\in K$, and $g(x_0)=0$. For every $\varepsilon>0$ there is $s_0>0$ such that $$f(x)+s g(x)\le\varepsilon s$$ for every $x\in K$ and $0<s<s_0$. This is the compactness step behind the $o(s)$ estimate in Lemma 5.6; only continuity on the compact cavity-law domain is required.
-- source:
--   Auxiliary analytic step in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6 using equation (29).

import Mathlib
set_option autoImplicit false
open Set

theorem ZeroFreeRRG.Hardcore.unique_maximum_small_perturbation_on {α : Type} [TopologicalSpace α] (K : Set α) (hK : IsCompact K)
    (f g : α → ℝ) (hf : ContinuousOn f K) (hg : ContinuousOn g K) (x₀ : α) (hx₀ : x₀ ∈ K)
    (hfnonpos : ∀ x ∈ K, f x ≤ 0) (_hfzero : f x₀ = 0)
    (hunique : ∀ x ∈ K, f x = 0 → x = x₀) (hgzero : g x₀ = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ s₀ : ℝ, 0 < s₀ ∧
      ∀ s : ℝ, 0 < s → s < s₀ → ∀ x ∈ K, f x + s * g x ≤ ε * s := by sorry
