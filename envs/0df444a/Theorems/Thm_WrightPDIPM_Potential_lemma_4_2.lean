-- Prove2me | Theorems.Thm_WrightPDIPM_Potential_lemma_4_2
-- name    : WrightPDIPM.Potential.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:04.702852+00:00
-- url     : https://prove2.me/theorems/32016b4f-2532-43c7-b61c-21037f0d6b9a
-- title:
--   Lemma 4.2 — Φ_n(x, s) ≥ n log n, with equality iff XSe = μe
-- statement:
--   Let $x, s \in \mathbb R^n$ be positive vectors, $\mu = x^Ts/n$, and let $\Phi_n(x,s) = n\log x^Ts - \sum_{i=1}^n\log x_is_i$ be the potential (4.2) with $\rho = n$. Then
--   $$\Phi_n(x,s) \ge n\log n,$$
--   with equality if and only if $XSe = (x^Ts/n)e = \mu e$, that is, $x_is_i = \mu$ for every $i$.
--
--   This shows that the centrality term $\Phi_n$ of the decomposition $\Phi_\rho = (\rho-n)\log x^Ts + \Phi_n$ (4.4a) is bounded below, with its minimum exactly on the points where all pairwise products agree.
--
--   **Formalization Note** `Phi (n : ℝ) x s` is $\Phi_n$. For $n = 0$ both sides are $0$ and the equality condition is empty, so the statement needs no hypothesis $n \ge 1$.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 68, Lemma 4.2

import Mathlib
import Definitions.Def_WrightPDIPM_Potential_Setting

open Matrix

namespace WrightPDIPM.Potential

/-- **Lemma 4.2** (Wright, p. 68). For a positive vector pair `(x, s) > 0`,
`Φ_n(x, s) ≥ n log n`, with equality if and only if `XSe = (xᵀs/n)e = μe`.
Here `Φ_n` is the potential (4.2) with `ρ = n`. -/
theorem lemma_4_2 {n : ℕ} (x s : Fin n → ℝ) (hx : ∀ i, 0 < x i) (hs : ∀ i, 0 < s i) :
    (n : ℝ) * Real.log n ≤ Phi (n : ℝ) x s ∧
      (Phi (n : ℝ) x s = (n : ℝ) * Real.log n ↔ ∀ i, x i * s i = mu x s) := by sorry

end WrightPDIPM.Potential
