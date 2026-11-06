-- Prove2me | Theorems.Thm_ZeroOneExpansion_lemma_9
-- name    : ZeroOneExpansion.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:59.963598+00:00
-- url     : https://prove2.me/theorems/f9802ae1-4590-40bf-b02a-5f9b61cf0cfc
-- title:
--   Lemma 9 — the one-block compatibility relation $\mathcal R$
-- statement:
--   Let $\mathcal R=\{(00,00),(10,10),(01,01),(11,10),(11,01)\}\subseteq C\times D$. For $(c,d)\in C\times D$, there exists $w\in\mathbb R^2$ for which $w\cdot x$ is uniquely maximized over $C$ at $c$ and over $D$ at $d$ if and only if $(c,d)\in\mathcal R$.
--
--   This is the one-block case of the cross-layer edge criterion.
--
--   Differences from the source:
--   - encoding: x ↦ w·x is uniquely maximized over A at a₀ → ∀ a ∈ A, a ≠ a₀ → w·a < w·a₀; reason: the definition of a unique maximizer
--   - encoding: the points 00, 10, 01, 11 of ℝ^2 → ![0,0], ![1,0], ![0,1], ![1,1]; reason: the paper's labels: 10 = e₁, 01 = e₂ (D = {0, e1, e2} = {00, 10, 01})
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), Lemma 9, p.5

import Mathlib
import Definitions.Def_ZeroOneExpansion_compatR

set_option autoImplicit false

open Matrix

namespace ZeroOneExpansion

/-- **Lemma 9** (Yang, *0/1-Polytopes with Exponentially Small Edge Expansion*, arXiv:2608.01870, p.5). For `(c, d) ∈ C × D`, there is `w ∈ ℝ^2` for which `w · x` is uniquely
maximized over `C` at `c` and over `D` at `d` iff `(c, d) ∈ R`, where
`R = {(00, 00), (10, 10), (01, 01), (11, 10), (11, 01)}`.

**Formalization Note** "Uniquely maximized over `C` at `c`" is `∀ x ∈ C, x ≠ c → w · x < w · c`.
`10 = (1, 0)` and `01 = (0, 1)`. -/
theorem lemma_9 (c₀ d₀ : Fin 2 → ℝ) (hc : c₀ ∈ C) (hd : d₀ ∈ D) :
    (∃ w : Fin 2 → ℝ, (∀ x ∈ C, x ≠ c₀ → w ⬝ᵥ x < w ⬝ᵥ c₀) ∧
        (∀ x ∈ D, x ≠ d₀ → w ⬝ᵥ x < w ⬝ᵥ d₀)) ↔
      (c₀, d₀) ∈ compatR := by sorry

end ZeroOneExpansion
