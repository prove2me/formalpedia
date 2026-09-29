-- Prove2me | Theorems.Thm_WindowMultiplicity_exists_forall_finite_and_le_pow_mul_ncard_stripRows
-- name    : WindowMultiplicity.exists_forall_finite_and_le_pow_mul_ncard_stripRows
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/af8600f3-5c43-5778-b777-8a8258f5d7f2
-- title:
--   Window count lower bound for generating vectors of a
-- statement:
--   Let $K$ be a number field, let $\mathfrak a$ and $\mathfrak n$ be nonzero ideals of the ring of integers $\mathcal O_K$, let $\kappa' > 1$ be real, and let $G$ be a compact set of families $g = (g_w)_w$ indexed by the infinite places $w$ of $K$, where $g_w$ is a $2\times 2$ matrix over the completion $K_w$, such that $\det(g_w) \neq 0$ for every $g \in G$ and every $w$. Then there exist $c_0 > 0$ and $\eta_0 > 0$ with the following property: for every pair $r_0 = (r_{0,1}, r_{0,2})$ of elements of $\mathfrak a$ with $\operatorname{span}\{r_{0,1}, r_{0,2}\} = \mathfrak a$, every real $\eta$ with $0 < \eta \le \eta_0$, and every $g \in G$, the set $S$ of pairs $p = (p_1,p_2)$ of elements of $\mathfrak a$ with $\operatorname{span}\{p_1,p_2\} = \mathfrak a$, satisfying $p_1 - r_{0,1} \in \mathfrak n\mathfrak a$ and $p_2 - r_{0,2} \in \mathfrak n\mathfrak a$, and such that for every infinite place $w$ the quantity
--   $$\frac{\lVert \det(g_w)\rVert}{\lVert p_1 (g_w)_{00} + p_2 (g_w)_{10}\rVert^2 + \lVert p_1 (g_w)_{01} + p_2 (g_w)_{11}\rVert^2}$$
--   (the images of $p_1,p_2$ in $K_w$ being understood) lies in the window $[\eta,\ \kappa'\eta]$, is finite and satisfies $c_0 \le \eta^{[K:\mathbb Q]}\,\lvert S\rvert$.
--
--   This is the counting estimate that, for a fixed congruence class modulo $\mathfrak n\mathfrak a$, produces at least $c_0\,\eta^{-[K:\mathbb Q]}$ generating vectors of $\mathfrak a$ whose local heights at all infinite places simultaneously lie in a fixed multiplicative window of width $\kappa'$ around $\eta$, with constants uniform in the class, in the window level and in the matrix family. It is used in the analysis of class sums for automorphic forms, where such a lower bound on the number of contributing vectors converts a window mass bound into a growth statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WindowMultiplicity_exists_forall_finite_and_le_pow_mul_ncard_stripRows.lean

import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem WindowMultiplicity.exists_forall_finite_and_le_pow_mul_ncard_stripRows (K : Type) [Field K]
    [NumberField K] (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) (𝔫 : Ideal (𝓞 K)) (h𝔫 : 𝔫 ≠ ⊥) (κ' : ℝ) (hκ' : 1 < κ')
    (G : Set ((w : InfinitePlace K) → Matrix (Fin 2) (Fin 2) w.Completion)) (hG : IsCompact G)
    (hdet : ∀ g ∈ G, ∀ w, (g w).det ≠ 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ r₀ : 𝓞 K × 𝓞 K,
      (r₀.1 ∈ 𝔞 ∧ r₀.2 ∈ 𝔞 ∧ Ideal.span {r₀.1, r₀.2} = 𝔞) → ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ g ∈ G,
        ({p : 𝓞 K × 𝓞 K | (p.1 ∈ 𝔞 ∧ p.2 ∈ 𝔞 ∧ Ideal.span {p.1, p.2} = 𝔞) ∧
            p.1 - r₀.1 ∈ 𝔫 * 𝔞 ∧ p.2 - r₀.2 ∈ 𝔫 * 𝔞 ∧
            ∀ w : InfinitePlace K,
            η ≤ ‖(g w).det‖ /
              (‖algebraMap K w.Completion (p.1 : K) * g w 0 0 + algebraMap K w.Completion (p.2 : K) * g w 1 0‖ ^ 2 +
                ‖algebraMap K w.Completion (p.1 : K) * g w 0 1 + algebraMap K w.Completion (p.2 : K) * g w 1 1‖ ^ 2) ∧
            ‖(g w).det‖ /
              (‖algebraMap K w.Completion (p.1 : K) * g w 0 0 + algebraMap K w.Completion (p.2 : K) * g w 1 0‖ ^ 2 +
                ‖algebraMap K w.Completion (p.1 : K) * g w 0 1 + algebraMap K w.Completion (p.2 : K) * g w 1 1‖ ^ 2) ≤
              κ' * η}).Finite ∧
        c₀ ≤ η ^ Module.finrank ℚ K *
          (({p : 𝓞 K × 𝓞 K | (p.1 ∈ 𝔞 ∧ p.2 ∈ 𝔞 ∧ Ideal.span {p.1, p.2} = 𝔞) ∧
            p.1 - r₀.1 ∈ 𝔫 * 𝔞 ∧ p.2 - r₀.2 ∈ 𝔫 * 𝔞 ∧
            ∀ w : InfinitePlace K,
            η ≤ ‖(g w).det‖ /
              (‖algebraMap K w.Completion (p.1 : K) * g w 0 0 + algebraMap K w.Completion (p.2 : K) * g w 1 0‖ ^ 2 +
                ‖algebraMap K w.Completion (p.1 : K) * g w 0 1 + algebraMap K w.Completion (p.2 : K) * g w 1 1‖ ^ 2) ∧
            ‖(g w).det‖ /
              (‖algebraMap K w.Completion (p.1 : K) * g w 0 0 + algebraMap K w.Completion (p.2 : K) * g w 1 0‖ ^ 2 +
                ‖algebraMap K w.Completion (p.1 : K) * g w 0 1 + algebraMap K w.Completion (p.2 : K) * g w 1 1‖ ^ 2) ≤
              κ' * η}).ncard : ℝ) := by sorry
