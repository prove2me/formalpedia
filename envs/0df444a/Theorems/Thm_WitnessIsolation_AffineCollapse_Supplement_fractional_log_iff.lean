-- Prove2me | Theorems.Thm_WitnessIsolation_AffineCollapse_Supplement_fractional_log_iff
-- name    : WitnessIsolation.AffineCollapse.Supplement.fractional_log_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:56:54.393326+00:00
-- url     : https://prove2.me/theorems/a22b2ad4-058b-43f4-92f0-f71a8da59816
-- title:
--   Theorem 7.3 — Fractional-logarithm guarantees c/R_q(n)^a are equivalent to NP ⊆ P/poly
-- statement:
--   Fix an integer $q\ge1$ and reals $a,c>0$, and let $R_q$ be the fractional iterate of the logarithm of §7.1. Then:
--
--   1. a pruning transformation with (affine) witness-length guarantee
--   $$p(n)\ge\frac{c}{R_q(n)^a}$$
--   exists if and only if $\mathrm{NP}\subseteq\mathrm{P/poly}$;
--   2. for $q\ge2$ this guarantee is eventually smaller than $2^{-C(\log\log n)^b}$ for all fixed $b,C$: for every $b,C$ there is $N$ with
--   $$\frac{c}{R_q(n)^a}<2^{-C(\log\log n)^b}\qquad(n\ge N).$$
--
--   With $q+1$ steps of the recurrence instead of two, the collapse extends from the guarantees of Theorem 1.1 to strictly smaller ones.
--
--   **Formalization Note** "Some transformation has guarantee $p\ge c/R_q^a$" is stated as `HasGuarantee I (fractionalRate q a c)`; the guarantee predicate is monotone in $p$, so the two are equivalent. Logarithms are `Real.logb 2`.
--
--   Differences from the source:
--   - encoding: some pruning transformation has witness-length guarantee p with p(n) ≥ c/R_q(n)^a → ∃ I, IsPruner I ∧ HasGuarantee I (n ↦ c/R_q(n)^a); reason: the published guarantee is monotone in the rate, so the forms are equivalent
--   - reading: for all fixed b, C → for all real b and C; reason: the source gives no range; negative or zero values are the easy cases
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), p. 13, PDF p. 14, Theorem 7.3; proof p. 14, PDF p. 15

import Definitions.Def_WitnessIsolation_AffineCollapse_Supplement_fractional_log

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse.Supplement

/-- Theorem 7.3, printed p. 13 / PDF p. 14; proof printed p. 14 / PDF p. 15. For every
integer `q ≥ 1` and real `a, c > 0`: a pruning transformation with witness-length guarantee
`c/R_q(n)^a` exists iff NP ⊆ P/poly; and for `q ≥ 2` this guarantee is eventually strictly
below `2^{-C (log log n)^b}` for all real `b, C`. -/
theorem fractional_log_iff (q : ℕ) (hq : 1 ≤ q) (a c : ℝ)
    (ha : 0 < a) (hc : 0 < c) :
    ((∃ I : PruningFamily, IsPruner I ∧ HasGuarantee I (fractionalRate q a c)) ↔
      NPCollapse) ∧
    (2 ≤ q → ∀ b C : ℝ,
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        fractionalRate q a c n <
          (2:ℝ)^(-C*(Real.logb 2 (Real.logb 2 (n:ℝ)))^b)) := by sorry

end WitnessIsolation.AffineCollapse.Supplement
