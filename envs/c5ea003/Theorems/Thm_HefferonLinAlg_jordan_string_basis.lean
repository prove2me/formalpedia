-- Prove2me | Theorems.Thm_HefferonLinAlg_jordan_string_basis
-- name    : HefferonLinAlg.jordan_string_basis
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T15:06:00.585352+00:00
-- url     : https://prove2.me/theorems/33812c8a-3aec-4994-a5d9-78e2287c5d45
-- title:
--   Jordan basis: every complex linear map has a basis of Jordan strings
-- statement:
--   ## Statement
--
--   Let $V$ be a finite-dimensional complex vector space and $f : V \to V$ a linear map. Then $V$ has a **Jordan basis** for $f$: there are a number of strings $k$, string lengths $s_0,\dots,s_{k-1}$ with $s_i \ge 1$, eigenvalues $\lambda_0,\dots,\lambda_{k-1} \in \mathbb{C}$, and a basis of $V$
--   $$\bigl\{\, b_{i,a} \;:\; 0 \le i < k,\ 0 \le a < s_i \,\bigr\}$$
--   indexed by (string index, position along that string), such that
--   $$f\bigl(b_{i,a}\bigr) \;=\; \lambda_i\, b_{i,a} \;+\; \begin{cases} b_{i,\,a+1}, & a+1 < s_i,\\[3pt] 0, & a+1 = s_i.\end{cases}$$
--
--   In words: on the $i$-th string, $f$ acts as multiplication by $\lambda_i$ plus a shift one step along the string, and the last vector of each string is an honest eigenvector, $f(b_{i,s_i-1}) = \lambda_i\, b_{i,s_i-1}$.
--
--   ## Notes
--
--   This is the basis-level form of Jordan canonical form, and the direct source of its matrix form: written in the basis $b$, the matrix of $f$ is block diagonal, its $i$-th block being the $s_i \times s_i$ Jordan block with eigenvalue $\lambda_i$ — $\lambda_i$ down the diagonal and $1$'s on the subdiagonal. The pair (block sizes, eigenvalues) is exactly what the matrix statement calls the Jordan block data.
--
--   *Why the index type.* The basis is indexed by the dependent pair type $\Sigma_i\,\{0,\dots,s_i-1\}$, so that the block structure is carried by the index rather than reconstructed afterwards. Nothing forces the $\lambda_i$ to be distinct: a single eigenvalue may occur on many strings, which is what the presence of several blocks with the same eigenvalue means.
--
--   *Where the hypotheses are used.* Completeness of $\mathbb{C}$ is irrelevant; what matters is that $\mathbb{C}$ is algebraically closed, so that the characteristic polynomial splits and $V$ is the direct sum of the generalized eigenspaces of $f$. On each generalized eigenspace for $\lambda$, the map $f - \lambda$ is nilpotent, and a string basis for it is a Jordan string for $f$ with eigenvalue $\lambda$. Concatenating the strings over all eigenvalues gives the basis above. Over a field that is not algebraically closed the statement can fail — a rotation of the real plane has no eigenvector at all.
--
--   *Why $s_i \ge 1$.* Positive lengths are what make the multiset $\{(s_i,\lambda_i)\}$ an invariant of $f$; empty strings could otherwise be appended with arbitrary eigenvalues.
--
--   *Relation to Mathlib.* Mathlib provides the generalized eigenspace decomposition over an algebraically closed field, but no Jordan basis and no Jordan canonical form; this statement is the missing bridge between the two.
--
--   Hefferon, *Linear Algebra*, Chapter Five, Section IV.2, Theorem 2.8.
-- source:
--   Jim Hefferon, *Linear Algebra*, Saint Michael's College, 2020 printing, Chapter Five, Section IV.2, Theorem 2.8, printed p. 454 (PDF p. 464)

import Mathlib

namespace HefferonLinAlg

theorem jordan_string_basis
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) :
    ∃ (k : ℕ) (sz : Fin k → ℕ) (lam : Fin k → ℂ)
      (b : Module.Basis (Σ i : Fin k, Fin (sz i)) ℂ V),
      (∀ i, 0 < sz i) ∧
        ∀ (i : Fin k) (a : Fin (sz i)),
          f (b ⟨i, a⟩) =
            lam i • b ⟨i, a⟩ +
              (if h : (a : ℕ) + 1 < sz i then b ⟨i, ⟨(a : ℕ) + 1, h⟩⟩ else 0) := by
  sorry

end HefferonLinAlg
