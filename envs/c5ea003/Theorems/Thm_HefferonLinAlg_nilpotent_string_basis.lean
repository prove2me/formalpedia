-- Prove2me | Theorems.Thm_HefferonLinAlg_nilpotent_string_basis
-- name    : HefferonLinAlg.nilpotent_string_basis
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T15:00:12.111443+00:00
-- url     : https://prove2.me/theorems/9aca2a54-875d-49f3-8615-f7277723a141
-- title:
--   String basis for a nilpotent linear map
-- statement:
--   ## Statement
--
--   Let $V$ be a finite-dimensional vector space over a field $K$, and let $f : V \to V$ be a **nilpotent** linear map, i.e. $f^{\,m} = 0$ for some $m$. Then $V$ has a **string basis** for $f$: there are a number of strings $k$, string lengths $s_0,\dots,s_{k-1}$ with $s_i \ge 1$, and a basis of $V$
--   $$\bigl\{\, b_{i,a} \;:\; 0 \le i < k,\ 0 \le a < s_i \,\bigr\}$$
--   indexed by the pairs (string index, position along that string), such that $f$ advances every basis vector one step along its own string and annihilates the last vector of each string:
--   $$f\bigl(b_{i,a}\bigr) \;=\; \begin{cases} b_{i,\,a+1}, & a+1 < s_i,\\[3pt] 0, & a+1 = s_i.\end{cases}$$
--
--   Equivalently, $V$ decomposes as a direct sum of $f$-cyclic subspaces
--   $$V \;=\; \bigoplus_{i=0}^{k-1} \operatorname{span}\bigl\{\, b_{i,0},\, f b_{i,0},\, \dots,\, f^{\,s_i-1} b_{i,0} \,\bigr\},\qquad f^{\,s_i} b_{i,0} = 0 .$$
--
--   ## Notes
--
--   This is the structure theorem for a nilpotent linear map, and the technical heart of Jordan canonical form. Hefferon calls the chains $b_{i,0} \mapsto b_{i,1} \mapsto \cdots \mapsto 0$ **strings**, and a basis assembled from them a **string basis**; the picture is that $f$ shifts each string one place towards its end, where it dies.
--
--   *Why the statement is phrased this way.* The basis is indexed by the dependent pair type $\Sigma_i\, \{0,\dots,s_i-1\}$ rather than by $\{0,\dots,\dim V - 1\}$, so that the string structure is visible in the index itself: the first component names the string, the second the position in it. This is the same index type used by block-diagonal matrices, so the matrix of $f$ in this basis is literally block diagonal, its $i$-th block being the $s_i \times s_i$ nilpotent Jordan block (ones on the subdiagonal, zeros elsewhere). Reading the theorem that way turns it into "every nilpotent matrix is similar to a direct sum of nilpotent Jordan blocks".
--
--   *Why $s_i \ge 1$.* Without positivity of the lengths one could pad the data with empty strings, and the multiset of string lengths — which is the actual similarity invariant — would no longer be determined by $f$. The lengths themselves are recoverable from the kernel dimensions $\dim\ker f^{\,r}$.
--
--   *Generality.* No hypothesis of algebraic closure is needed: the theorem holds over an arbitrary field, because a nilpotent map has no eigenvalue other than $0$ and so no field extension is required. Algebraic closure enters only later, when one splits a general map into generalized eigenspaces before applying this result to $f - \lambda$ on each of them.
--
--   *Relation to Mathlib.* Mathlib knows a great deal about nilpotent endomorphisms and about generalized eigenspaces, but does not provide a string basis, a cyclic decomposition for a nilpotent map, or Jordan canonical form; this statement fills that gap and is intended to be reused for both.
--
--   Hefferon, *Linear Algebra*, Chapter Five, Section III.2 (Strings), Theorem 2.16 and Corollary 2.17.
-- source:
--   Jim Hefferon, *Linear Algebra*, Saint Michael's College, 2020 printing, Chapter Five, Section III.2 (Strings), Theorem 2.16 and Corollary 2.17, printed pp. 434-435 (PDF pp. 444-445)

import Mathlib

namespace HefferonLinAlg

theorem nilpotent_string_basis
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (hf : IsNilpotent f) :
    ∃ (k : ℕ) (sz : Fin k → ℕ) (b : Module.Basis (Σ i : Fin k, Fin (sz i)) K V),
      (∀ i, 0 < sz i) ∧
        ∀ (i : Fin k) (a : Fin (sz i)),
          f (b ⟨i, a⟩) =
            if h : (a : ℕ) + 1 < sz i then b ⟨i, ⟨(a : ℕ) + 1, h⟩⟩ else 0 := by
  sorry

end HefferonLinAlg
