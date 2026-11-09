-- Prove2me | Theorems.Thm_ZamirInversion581_Mult_lemma_2_5
-- name    : ZamirInversion581.Mult.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:47.481245+00:00
-- url     : https://prove2.me/theorems/1f995f39-7cf2-460e-ba87-b8b63842a6c8
-- title:
--   Lemma 2.5 — any positive average success amplifies to $1-\delta$ at cost $O(s(T(n)+n^2r+nr^2+r^3+dn^2))$
-- statement:
--   Let $F$ be a finite field with $q$ elements. There is an absolute constant $c>0$ such that for every $F$ there is one program $P$ of the field-operation machine with the following property. Let $n\ge0$, $\varepsilon>0$, $0<\delta<1/2$, let $I$ be an inversion oracle whose average success on $\mathrm{GL}_n(F)$ is at least $\varepsilon$, and let $s,r,d$ be naturals with
--
--   $$
--   s\ge\frac8\varepsilon\ln\frac3\delta,\qquad q^{2r}\ge\frac{192}{\varepsilon\delta},\qquad q^d\ge\frac{3s}\delta.
--   $$
--
--   Given $n,s,r,d$ in its index registers and an $n\times n$ matrix $X$ in memory:
--
--   1. on every $X$, every run halts with at most $s$ oracle calls, all in dimension $n$, and at most $c\,s\,(1+n^2r+nr^2+r^3+dn^2)$ other operations;
--   2. the mean over $X\in\mathrm{GL}_n(F)$ of the probability that the output is $X^{-1}$ is at least $1-\delta$.
--
--   Charging $T(n)$ per call, the running time is $O(s(T(n)+n^2r+nr^2+r^3+dn^2))$. So any inverter with positive average success yields one with average success close to $1$, at an overhead near-linear in $1/\varepsilon$ with logarithmic factors in $1/\delta$.
--
--   Differences from the source:
--   - reading: running time Õ_{ε,δ}(T(n) + n²), overhead near-linear in 1/ε and logarithmic in 1/δ → at most s calls and ops ≤ c·s·(1 + n²r + nr² + r³ + dn²); reason: this is the proof's displayed cost O(s(T(n) + n²r + nr² + r³ + dn²)), p.10; the lemma's word “logarithmic” is read as the logarithmic factors in that explicit bound, not as a separate sharp linear-log bound in 1/δ
--   - generalization: s = ⌈(8/ε) ln(3/δ)⌉, r = ⌈½ log_q(192/(εδ))⌉, d = ⌈log_q(3s/δ)⌉ → any naturals s, r, d satisfying the three inequalities, passed as input; reason: the printed ceilings are the least values satisfying the inequalities, so they are an instance; a program cannot compute the exact real ceiling at unit cost but can compute a larger valid value
--   - generalization: for given ε, δ there is an algorithm → one program for all n, ε, δ, I, with c absolute; reason: the printed algorithm is the instance at given parameters; the proof's algorithm does not depend on them except through s, r, d
--   - generalization: a randomized algorithm running in time T(m) → any oracle family I, with any T charged per call; reason: a time-T algorithm is one such pair; charging T per call and counting the program's own instructions is its running time
--   - reading: an unnamed computation model → the finite-program field-operation machine of the Machine definition; reason: p.11 "The running times count field operations"; index instructions are charged too, which only makes the bound more demanding
--   - encoding: O(·) → absolute c and the summand 1; reason: the hypotheses force r ≥ 1, so r³ ≥ 1 and the summand changes the bound by a factor of at most 2
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.10, Lemma 2.5 and the display of its cost; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform
import Definitions.Def_ZamirInversion581_Mult_Inverter
import Definitions.Def_ZamirInversion581_Mult_Machine

set_option autoImplicit false

namespace ZamirInversion581.Mult

/-- Lemma 2.5, p.10. Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256
175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917. "Suppose I_n correctly computes the
inverse of a uniform matrix in GL_n(F_q) with probability at least ε. For any 0 < δ < 1/2, there is
an algorithm I_n⁺ whose average success on GL_n(F_q) is at least 1 − δ and whose running time is
Õ_{ε,δ}(T(n) + n²). For variable ε, δ, the overhead is near-linear in 1/ε and logarithmic in 1/δ."

**Formalization Note.** The cost is the proof's display `O(s(T(n) + n²r + nr² + r³ + dn²))`, p.10:
at most `s` calls in dimension `n`, and `ops` bounded by the rest. The absolute constant `c` precedes
the field; the program `P` is chosen for the field only and reads `n, s, r, d` from index registers
`0, 1, 2, 3`, with `X` stored row-major from address `0`. The proof's `s = ⌈(8/ε) ln(3/δ)⌉`,
`r = ⌈½ log_q (192/(εδ))⌉`, `d = ⌈log_q (3s/δ)⌉` are the least naturals satisfying the three
inequalities assumed here. -/
theorem lemma_2_5 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F],
        ∃ P : Program F,
          ∀ (n : ℕ) (ε δ : ℝ) (I : InversionOracle F) (s r d : ℕ),
            0 < ε → 0 < δ → δ < 1 / 2 →
            (8 / ε) * Real.log (3 / δ) ≤ (s : ℝ) →
            192 / (ε * δ) ≤ (Fintype.card F : ℝ) ^ (2 * r) →
            3 * (s : ℝ) / δ ≤ (Fintype.card F : ℝ) ^ d →
            ε ≤ inverterSuccess I n →
            ∃ N : ℕ,
              (∀ X : Matrix (Fin n) (Fin n) F,
                ∀ σ ∈ (run n I P N (invInput n [n, s, r, d] X)).support,
                  σ.status ≠ .running ∧
                  σ.calls n ≤ s ∧
                  (∀ m, m ≠ n → σ.calls m = 0) ∧
                  (σ.ops : ℝ) ≤ c * (s : ℝ) *
                    (1 + (n : ℝ) ^ 2 * r + (n : ℝ) * (r : ℝ) ^ 2 + (r : ℝ) ^ 3 +
                      (d : ℝ) * (n : ℝ) ^ 2)) ∧
              1 - δ ≤ unifMean fun X : Matrix.GeneralLinearGroup (Fin n) F =>
                outputProb n I P (invInput n [n, s, r, d] (X : Matrix (Fin n) (Fin n) F)) N
                  ((X⁻¹ : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) := by sorry

end ZamirInversion581.Mult
