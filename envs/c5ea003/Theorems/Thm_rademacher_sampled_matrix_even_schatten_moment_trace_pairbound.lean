-- Prove2me | Theorems.Thm_rademacher_sampled_matrix_even_schatten_moment_trace_pairbound
-- name    : rademacher_sampled_matrix_even_schatten_moment_trace_pairbound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-23T21:25:05.171715+00:00
-- url     : https://prove2.me/theorems/af7c38b7-d260-499f-84ed-4c716935ca3c
-- statement:
--   **Even-integer Schatten-moment Khintchine bound (the matched-moment assembly step).** For the symmetrized coordinate Rademacher series $S_\varepsilon = \texttt{rademacherSampledMatrix}\,\Omega\,\varepsilon\,p\,X$ and every integer $n\ge1$, the sign-averaged even Schatten moment of exponent $2n$ is bounded by the pair-partition count times the larger diagonal-Gram Schatten term:
--
--   $$\mathbb{E}_{\varepsilon}\big[\,\|S_\varepsilon\|_{S_{2n}}^{\,2n}\,\big]\;\le\;\frac{(2n)!}{2^{n} n!}\;\max\Big(\big(\texttt{sampledRowGramSchatten}\,\Omega\,p\,X\,(2n)\big)^{2n},\;\big(\texttt{sampledColumnGramSchatten}\,\Omega\,p\,X\,(2n)\big)^{2n}\Big).$$
--
--   This is the clean assembly of two pieces: (i) the even-integer trace-moment identity $\|S\|_{S_{2n}}^{2n} = \operatorname{tr}((S S^{\top})^n)$ (applied pointwise inside the finite sign average), and (ii) Buchholz's combinatorial trace pairbound $\mathbb{E}_\varepsilon[\operatorname{tr}((S S^\top)^n)] \le \frac{(2n)!}{2^n n!}\max(\dots)$. It is the even-$q$ case of the noncommutative Khintchine inequality; the general real-$q$ case ($q\ge2$, $q\ge\beta\log n$) follows by the operator-norm sandwich $\|S\|_{S_q}\le e\|S\|\le e\|S\|_{S_{2n}}$ and a power-mean (Jensen) step.  Source: Buchholz, *Operator Khintchine inequality in non-commutative probability*, Math. Ann. 319 (2001) 1–16, §2–3; CR2009 (arXiv:0805.4471) §6.1 Lemma 6.1.
-- source:
--   Buchholz, Operator Khintchine inequality in non-commutative probability, Math. Ann. 319 (2001) 1-16, sections 2-3; CR2009 (arXiv:0805.4471) section 6.1 Lemma 6.1

import Definitions.Def_matrix_completion_gram_schatten
open MatrixCompletion
open scoped BigOperators

theorem rademacher_sampled_matrix_even_schatten_moment_trace_pairbound
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps =>
          schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n))
      ≤ ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) *
          max ((sampledRowGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n))
              ((sampledColumnGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n)) := by sorry
