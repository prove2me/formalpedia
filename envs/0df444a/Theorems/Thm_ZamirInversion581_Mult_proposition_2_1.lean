-- Prove2me | Theorems.Thm_ZamirInversion581_Mult_proposition_2_1
-- name    : ZamirInversion581.Mult.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:26.878716+00:00
-- url     : https://prove2.me/theorems/52da9cff-31d5-4c83-bac9-31461bd660b0
-- title:
--   Proposition 2.1 — inversion with success $1-10^{-6}$ at $n,2n$ multiplies any two matrices in time $\tilde O(T(n)+T(2n)+n^2)$
-- statement:
--   There are absolute constants $c>0$ and $a\in\mathbb N$ such that for every finite field $F$ there is one program $P$ of the field-operation machine with the following property. Let $n\ge3$, $0<\kappa\le1/2$, $K=\lceil1/\kappa\rceil$, let $T:\mathbb N\to\mathbb R_{\ge0}$ be arbitrary, and let $I$ be an inversion oracle with average success at least $1-10^{-6}$ on $\mathrm{GL}_n(F)$ and on $\mathrm{GL}_{2n}(F)$. Then for all $B,C\in F^{n\times n}$:
--
--   1. every run halts with total time at most $c\,(\log(2nK))^a\,(T(n)+T(2n)+n^2)$;
--   2. the run outputs exactly $BC$ with probability at least $1-\kappa$.
--
--   This is the worst-case multiplication algorithm obtained from a high-success average-case inverter. Theorem 1.1 uses it together with the amplification of Lemma 2.5.
--
--   Differences from the source:
--   - generalization: a randomized algorithm running in time T(m) → any oracle family I, with any T charged per call; reason: a time-T algorithm is one such pair; charging T per call and counting the program's own instructions is its running time
--   - reading: an unnamed computation model → the finite-program field-operation machine of the Machine definition; reason: p.11 "The running times count field operations"; index instructions are charged too, which only makes the bound more demanding
--   - reading: "with high probability" → every κ ∈ (0, 1/2], with K = ⌈1/κ⌉ as input; reason: the inverse-polynomial case is κ = n^(−c), with K polynomial in n
--   - reading: Õ(T(n) + T(2n) + n²) → c·log(2nK)^a·(T(n) + T(2n) + n²) with absolute c and natural a; reason: p.6 "All estimates in this section are uniform in the field size q"; log(2nK) ≥ log 12 > 1, so a natural exponent loses nothing
--   - generalization: an algorithm for the given n → one program for all n, κ, I, T; reason: the source's algorithm is the instance at given parameters
--   - encoding: n ≥ 3 stated once in the section → the hypothesis 3 ≤ n; reason: standing assumption of §2.1, p.6
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.6, Proposition 2.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform
import Definitions.Def_ZamirInversion581_Mult_Inverter
import Definitions.Def_ZamirInversion581_Mult_Machine

set_option autoImplicit false

namespace ZamirInversion581.Mult

/-- Proposition 2.1, p.6. Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256
175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917. "Suppose that for m = n, 2n the
algorithm I_m runs in time T(m) and correctly inverts a uniformly random matrix on GL_m(F_q) with
probability at least 1 − 10⁻⁶. Then any two matrices in F_q^{n×n} can be multiplied with high
probability in time Õ(T(n) + T(2n) + n²)."

**Formalization Note.** `c, a` are absolute and precede the field; the program `P` is chosen for the
field only and reads `n, K` from index registers `0, 1`, where `K = ⌈1/κ⌉`, with `B` stored row-major
from address `0` and `C` from address `n²`. `n ≥ 3` is the standing assumption of §2.1 (p.6). -/
theorem proposition_2_1 :
    ∃ (c : ℝ) (a : ℕ), 0 < c ∧
      ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F],
        ∃ P : Program F,
          ∀ (n : ℕ) (κ : ℝ) (I : InversionOracle F) (T : ℕ → NNReal),
            3 ≤ n → 0 < κ → κ ≤ 1 / 2 →
            1 - (1 : ℝ) / 10 ^ 6 ≤ inverterSuccess I n →
            1 - (1 : ℝ) / 10 ^ 6 ≤ inverterSuccess I (2 * n) →
            ∀ B C : Matrix (Fin n) (Fin n) F,
              let K : ℕ := ⌈1 / κ⌉₊
              ∃ N : ℕ,
                AllRunsHaltWithin n I P (multInput n [n, K] B C) N T
                  (c * (Real.log (2 * (n : ℝ) * (K : ℝ))) ^ a *
                    ((T n : ℝ) + (T (2 * n) : ℝ) + (n : ℝ) ^ 2)) ∧
                1 - κ ≤ outputProb n I P (multInput n [n, K] B C) N (B * C) := by sorry

end ZamirInversion581.Mult
