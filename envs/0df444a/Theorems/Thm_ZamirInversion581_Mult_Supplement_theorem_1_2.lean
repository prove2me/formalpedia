-- Prove2me | Theorems.Thm_ZamirInversion581_Mult_Supplement_theorem_1_2
-- name    : ZamirInversion581.Mult.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:51:33.533258+00:00
-- url     : https://prove2.me/theorems/30365077-3b71-4317-af75-7adf6e5504ad
-- title:
--   Theorem 1.2 — conditional rank and invertibility reductions
-- statement:
--   Fix a finite field $F$ and a trapdoored-matrix family as in §3.1. There are $c>0$ and $a\in\mathbb N$, depending only on this field and family, with the following property. Let $\varepsilon>0$ and let $A$ be one polynomial-time field-RAM program whose every run on an $n\times n$ input takes at most $T(n)$ field operations. Assume, for every sufficiently large $n$, either of the following alternatives (one alternative holds throughout those dimensions):
--
--   1. Its invertibility-bit success on a uniform matrix is at least $\max\{s_{q,n},1-s_{q,n}\}+\varepsilon$, where $s_{q,n}$ is the singularity probability.
--   2. Its exact-rank success on a uniform matrix is at least $\max_{0\le r\le n}\Pr[\operatorname{rank}X=r]+\varepsilon$.
--
--   For each $0<\kappa\le1/2$ there are finite programs for worst-case invertibility and exact rank, with dimension thresholds, such that on every matrix above the corresponding threshold all runs halt within the respective bounds
--   $$
--   c\varepsilon^{-2}(T(n)+n^2)\log(2nEK)^a,\qquad c\varepsilon^{-2}(T(2n)+n^2)\log(2nEK)^a,
--   $$
--   and their correct-output probabilities are at least $1-\kappa$. Here $E=\lceil1/\varepsilon\rceil$ and $K=\lceil1/\kappa\rceil$. The constants precede $\varepsilon,A,T,\kappa$; the programs and thresholds may depend on them. No monotonicity of $T$ is assumed.
--
--   This companion theorem establishes both worst-case consequences from either advantage over the best constant predictor.
--
--   Differences from the source:
--   - reading: algorithms and running times count field operations → one finite oracle-free randomized field-RAM program, with all supported runs bounded; reason: the source specifies field operations on p.11; one common model makes the polynomial-time pseudorandomness hypothesis applicable
--   - reading: asymptotic Õ_q(ε⁻²(T(n)+n²)) and rank cost at 2n → c ε⁻²(T(n)+n²) log(2nEK)^a and the corresponding T(2n) bound, with c,a after the field and family but before ε,A,T,κ; reason: explicit uniform constants and dimension thresholds express the asymptotic statement without adding conditions on T
--   - reading: with high probability → each failure target 0<κ≤1/2, with K=ceil(1/κ) supplied as an index input; reason: pp.17–18 give logarithmic statistical amplification; inverse-polynomial failure is included
--   - encoding: uniform n by n matrices and bit or rank answers → Fin n rows and columns, integer bits 0/1 and integer ranks, with all other outputs incorrect; reason: these are the same finite objects and success events
--   - reading: hypothesis (i) or (ii) at dimension n, range of n unstated → (i) for every n ≥ N₀, or (ii) for every n ≥ N₀; reason: this is the stronger of the two readings (it is implied by the every-n reading), matching the base goal's 'for all sufficiently large m'; the Õ conclusions are asymptotic and are claimed for n ≥ n₀
--   - reading: a trapdoored-matrix family of samplers indexed by n with Õ(n²) sampling and Õ(n) action (p.11) → one sampler program and one action program of the field RAM taking n as input, with constants C, b of the family, and c, a allowed to depend on the family; reason: the reductions are uniform algorithms that draw trapdoored matrices at every dimension (pp.17–19), and the polylogarithmic exponents of the family enter the Õ_q bound
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.3, Theorem 1.2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Supplement_Reductions

set_option autoImplicit false

namespace ZamirInversion581.Mult.Supplement

/-- Theorem 1.2, p.3. Constants may depend only on the fixed field and trapdoor family.
Both alternative average-case hypotheses and both worst-case conclusions are retained. -/
theorem theorem_1_2 (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (𝒯 : TrapdoorPrograms F) (h𝒯 : IsTrapdoored 𝒯) :
    ∃ (c : ℝ) (a : ℕ), 0 < c ∧
      ∀ (ε : ℝ), 0 < ε → ∀ (A : Program F) (T : ℕ → NNReal) (N₀ : ℕ),
        PolyTime A → TimeBound A T → AboveBaseline A ε N₀ →
        ∀ κ : ℝ, 0 < κ → κ ≤ 1 / 2 → RankAndInvertibility (F := F) c a ε κ T := by sorry

end ZamirInversion581.Mult.Supplement
