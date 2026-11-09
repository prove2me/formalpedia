-- Prove2me | Theorems.Thm_ZamirInversion581_Mult_theorem_1_1
-- name    : ZamirInversion581.Mult.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:37.061816+00:00
-- url     : https://prove2.me/theorems/c9755532-ad62-4b82-ac5e-5d856c8b7ea3
-- title:
--   Theorem 1.1 — average-case inversion on an $\varepsilon$ fraction of $\mathrm{GL}_m(F_q)$ gives worst-case multiplication in time $\tilde O(T(2n)/\varepsilon)$
-- statement:
--   There are absolute constants $c>0$ and $a\in\mathbb N$ such that for every finite field $F$ there is one program $P$ of the field-operation machine with the following property. Let $\varepsilon>0$, $0<\kappa\le1/2$, $n\ge3$, and put $E=\lceil1/\varepsilon\rceil$, $K=\lceil1/\kappa\rceil$. Let $T:\mathbb N\to\mathbb R_{\ge0}$ satisfy
--
--   $$
--   n^2\le T(n)\le T(2n),\qquad (2n)^2\le T(2n),
--   $$
--
--   and let $I$ be an inversion oracle with
--
--   $$
--   \Pr_{Y\sim\mathrm{GL}_m(F)}[I_m(Y)=Y^{-1}]\ge\varepsilon\qquad\text{for }m=n\text{ and }m=2n.
--   $$
--
--   Then for all $B,C\in F^{n\times n}$, on input $n,E,K$ and $B,C$:
--
--   1. every run halts with total time at most $c\,\varepsilon^{-1}\,T(2n)\,(\log(2nEK))^a$, with the natural logarithm;
--   2. the run outputs exactly $BC$ with probability at least $1-\kappa$.
--
--   The inverter is any randomized map, each of its calls is charged $T$ at the dimension actually read, and it may answer anything on singular inputs. So an inverter succeeding on any positive fraction of random invertible matrices already captures the exponent of worst-case matrix multiplication, uniformly over finite fields.
--
--   **Formalization Note** The constants $c,a$ precede the field, and $P$ precedes $\varepsilon,\kappa,n,I,T$. A family of programs indexed by $n$ or a decision tree would make the statement trivial over small fields, so this order is part of its content.
--
--   Differences from the source:
--   - generalization: a randomized algorithm running in time T(m) → any oracle family I, with any T charged per call; reason: a time-T algorithm is one such pair; charging T per call and counting the program's own instructions is its running time
--   - generalization: hypothesis for all sufficiently large m, with T non-decreasing and T(m) ≥ m² → hypothesis only at m = n, 2n, and T's conditions only at n, 2n; reason: it specializes to the source at every n ≥ max(3, threshold); Õ is an asymptotic claim in n, so smaller n carry no content
--   - generalization: one algorithm for a fixed ε → one program for all ε, κ, n, I, T; reason: the source's algorithm is the instance at given ε
--   - reading: "with high probability" → every κ ∈ (0, 1/2]; reason: the proof on p.11 gives "inverse-polynomial", which is κ = n^(−c), with K polynomial in n
--   - reading: Õ((1/ε) T(2n)) → c·ε⁻¹·T(2n)·log(2nEK)^a with absolute c and natural a; reason: p.2 "uniformly over finite fields", p.6 "uniform in the field size q", and Õ here has no subscript q; with κ = n^(−c) this is polylog(n/ε); log(2nEK) ≥ log 12 > 1, so a natural exponent loses nothing
--   - reading: an unnamed computation model → the finite-program field-operation machine of the Machine definition; reason: p.11 "The running times count field operations"; index instructions are charged too, which only makes the bound more demanding
--   - encoding: n ≥ 3 stated at p.6; ε and the failure target known to the algorithm → the hypothesis 3 ≤ n; E and K passed in index registers; reason: the source fixes ε before its algorithm; ε ≤ 1 follows from the hypothesis and is not added
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.2, Theorem 1.1; p.6 standing assumption of §2.1; p.11 proof of Theorem 1.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform
import Definitions.Def_ZamirInversion581_Mult_Inverter
import Definitions.Def_ZamirInversion581_Mult_Machine

set_option autoImplicit false

namespace ZamirInversion581.Mult

/-- Theorem 1.1, p.2. Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256
175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917. "Let F_q be a finite field and
ε > 0. Suppose that for all sufficiently large m, a randomized algorithm I_m, running in some
non-decreasing time T(m) ≥ m², satisfies Pr_{Y∼GL_m(F_q)}[I_m(Y) = Y⁻¹] ≥ ε. Then any matrices
B, C ∈ F_q^{n×n} can be multiplied, with high probability, in time Õ((1/ε) T(2n))."

**Formalization Note.** The quantifier order is part of the statement. `c, a` are absolute and precede
the field. The single finite program `P` depends on the field only and precedes `ε, κ, n, I, T`; it
reads `n, E, K` from index registers `0, 1, 2`, where `E = ⌈1/ε⌉` and `K = ⌈1/κ⌉`, with `B` stored
row-major from address `0` and `C` from address `n²`. The time bound holds for every configuration in
the support, and the output is exactly `B C` with probability at least `1 − κ`, for every `B, C`. -/
theorem theorem_1_1 :
    ∃ (c : ℝ) (a : ℕ), 0 < c ∧
      ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F],
        ∃ P : Program F,
          ∀ (ε κ : ℝ) (n : ℕ) (I : InversionOracle F) (T : ℕ → NNReal),
            0 < ε → 0 < κ → κ ≤ 1 / 2 → 3 ≤ n →
            (n : NNReal) ^ 2 ≤ T n → T n ≤ T (2 * n) → (2 * (n : NNReal)) ^ 2 ≤ T (2 * n) →
            ε ≤ inverterSuccess I n →
            ε ≤ inverterSuccess I (2 * n) →
            ∀ B C : Matrix (Fin n) (Fin n) F,
              let E : ℕ := ⌈1 / ε⌉₊
              let K : ℕ := ⌈1 / κ⌉₊
              ∃ N : ℕ,
                AllRunsHaltWithin n I P (multInput n [n, E, K] B C) N T
                  (c * ε⁻¹ * (T (2 * n) : ℝ) *
                    (Real.log (2 * (n : ℝ) * (E : ℝ) * (K : ℝ))) ^ a) ∧
                1 - κ ≤ outputProb n I P (multInput n [n, E, K] B C) N (B * C) := by sorry

end ZamirInversion581.Mult
