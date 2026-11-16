-- Prove2me | Theorems.Thm_WitnessIsolation_AffineCollapse_Supplement_fractional_log_properties
-- name    : WitnessIsolation.AffineCollapse.Supplement.fractional_log_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:56:24.658464+00:00
-- url     : https://prove2.me/theorems/a840ad36-7e46-4292-a0e2-bc5587a34434
-- title:
--   Lemma 7.2 — Growth of the fractional logarithm R_q, with the identities of §7.1
-- statement:
--   Let $E_m$, $A$ and $R_q(x)=A^{-1}(A(x)-1/q)$ be as in §7.1 (logarithms base two). Then:
--
--   1. (§7.1) every $x\ge2$ is uniquely $E_m(u)$ with $m\ge0$, $2\le u<4$; $A$ is continuous and strictly increasing on $[2,\infty)$; $A(\log x)=A(x)-1$ for $x\ge4$; $A^{-1}$ inverts $A$ between $[2,\infty)$ and $[0,\infty)$; $R_1(x)=\log x$ and $R_q^{\circ q}(x)=\log x$ for $x\ge4$; and $R_q(\log x)=\log R_q(x)$ whenever $A(x)\ge1+1/q$.
--   2. (Lemma 7.2) For fixed $q\ge1$ there is $X$ such that for all $x\ge X$: $R_q$ is increasing on $[X,\infty)$; $R_q(Kx)\le K\,R_q(x)$ for every $K\ge1$; $R_q(x^a)\le R_q(x)^a$ for every $a\ge1$. Moreover $R_q(x)=x^{o(1)}$, i.e.
--   $$\frac{\log R_q(x)}{\log x}\to0\quad(x\to\infty).$$
--   3. (Lemma 7.2) For $q\ge2$, $R_q(x)/(\log x)^b\to\infty$ for every fixed real $b$.
--
--   $R_q$ lies strictly between all iterated logarithms of fixed depth and the logarithm itself, which is what makes Theorem 7.3 reach guarantees below those of Theorem 1.1.
--
--   **Formalization Note** $X$ is chosen before $K$ and $a$. Outside the source's domain $R_q$ takes the arbitrary value $2$ (see the definition); no clause depends on it.
--
--   Differences from the source:
--   - generalization: Lemma 7.2 (monotonicity, scaling, powers, x^{o(1)}, super-polylogarithmic growth for q ≥ 2) → the same clauses together with the identities the §7.1 paragraph asserts (unique tower representation, continuity and monotonicity of A, A(log x) = A(x) − 1, inverse identities, R_1 = log, R_q^{∘q} = log, R_q(log x) = log R_q(x)); reason: the source states these identities in the definition paragraph and the proof uses them; here they are proof obligations, never assumptions
--   - encoding: "for all large x" → one X ≥ 2, chosen before K and a, for the monotonicity, scaling and power clauses; reason: the eventual cutoff in the source does not depend on K or a
--   - encoding: R_q(x) = x^{o(1)} → log R_q(x) / log x → 0; reason: R_q(x) ≥ 2 eventually, so the two are equivalent
--   - reading: for every fixed b → for every real b; reason: b is not restricted in the source; b ≤ 0 is the trivial case
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), p. 13, PDF p. 14, Lemma 7.2 and the defining paragraph of §7.1

import Definitions.Def_WitnessIsolation_AffineCollapse_Supplement_fractional_log

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse.Supplement

/-- Lemma 7.2, printed p. 13 / PDF p. 14, together with the facts the defining paragraph of
§7.1 asserts about `A` and `R_q` (unique tower representation, `A` continuous and
increasing, `A(log x) = A(x) − 1`, `A⁻¹` inverse on `[0,∞)`, `R_1 = log`, `R_q^{∘q} = log`,
`R_q(log x) = log R_q(x)`), all as proof obligations. The eventual cutoff `X` of the
scaling and power inequalities precedes `K` and `a`. -/
theorem fractional_log_properties :
    (∀ x : ℝ, 2 ≤ x → ∃! z : ℕ × ℝ,
      2 ≤ z.2 ∧ z.2 < 4 ∧ x = tower z.1 z.2) ∧
    ContinuousOn abelCoordinate (Set.Ici 2) ∧
    StrictMonoOn abelCoordinate (Set.Ici 2) ∧
    (∀ x : ℝ, 4 ≤ x → abelCoordinate (Real.logb 2 x) = abelCoordinate x - 1) ∧
    (∀ x : ℝ, 2 ≤ x → abelInverse (abelCoordinate x) = x) ∧
    (∀ y : ℝ, 0 ≤ y → abelCoordinate (abelInverse y) = y) ∧
    (∀ x : ℝ, 4 ≤ x → fractionalLog 1 x = Real.logb 2 x) ∧
    (∀ q : ℕ, 1 ≤ q → ∀ x : ℝ, 4 ≤ x →
      (fractionalLog q)^[q] x = Real.logb 2 x) ∧
    (∀ q : ℕ, 1 ≤ q → ∀ x : ℝ, 2 ≤ x →
      1 + 1/(q:ℝ) ≤ abelCoordinate x →
      fractionalLog q (Real.logb 2 x) = Real.logb 2 (fractionalLog q x)) ∧
    (∀ q : ℕ, 1 ≤ q → ∃ X : ℝ, 2 ≤ X ∧
      StrictMonoOn (fractionalLog q) (Set.Ici X) ∧
      (∀ x : ℝ, X ≤ x → ∀ K : ℝ, 1 ≤ K →
        fractionalLog q (K*x) ≤ K*fractionalLog q x) ∧
      (∀ x : ℝ, X ≤ x → ∀ a : ℝ, 1 ≤ a →
        fractionalLog q (x^a) ≤ (fractionalLog q x)^a)) ∧
    (∀ q : ℕ, 1 ≤ q →
      Filter.Tendsto (fun x : ℝ => Real.logb 2 (fractionalLog q x) / Real.logb 2 x)
        Filter.atTop (nhds 0)) ∧
    (∀ q : ℕ, 2 ≤ q → ∀ b : ℝ,
      Filter.Tendsto (fun x : ℝ => fractionalLog q x / (Real.logb 2 x)^b)
        Filter.atTop Filter.atTop) := by sorry

end WitnessIsolation.AffineCollapse.Supplement
