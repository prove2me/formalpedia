-- Prove2me | Theorems.Thm_XOSMax_lemma_8_oracle_test
-- name    : XOSMax.lemma_8_oracle_test
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:24:37.90776+00:00
-- url     : https://prove2.me/theorems/ebdf0c3b-4ebd-4d1a-8f09-ce50cc9a0ef0
-- title:
--   Lemma 8 (proof) — the test $f(X+u)=f(X)+f(u)$ reads $I(X)\cap I(u)\ne\emptyset$
-- statement:
--   Let $f$ be represented by clauses $f_1,\dots,f_k$, with index sets $I(X)=\{i: f_i(X)=f(X)\}$. For every set $X$ and every $u\notin X$:
--
--   1. $f(X+u)=f(X)+f(u)$ if and only if $I(X)\cap I(u)\ne\emptyset$;
--   2. if $f(X+u)=f(X)+f(u)$ then $I(X+u)=I(X)\cap I(u)$.
--
--   This is the observation behind Algorithms 3 and 4: three oracle answers reveal whether a common clause attains $f$ at $X$ and at $u$, although the clauses are unknown.
--
--   Differences from the source:
--   - generalization: the current set $V_i$ of the algorithm, under the standing assumption $f(v)>0$ → an arbitrary set $X$, with no positivity hypothesis; reason: the argument uses neither, and the source claim is the instance $X=V_i$
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Lemma 8, proof, p.6, "The condition is satisfied if and only if"

import Mathlib
import Definitions.Def_XOSMax_Represents
import Definitions.Def_XOSMax_activeIndices

namespace XOSMax

/-- The oracle test in the proof of Lemma 8: for `u ∉ X`, "The condition is satisfied if and only if
I(Vi) ∩ I(u) ≠ ∅, and if satisfied, then I(Vi + u) = I(Vi) ∩ I(u) holds" (Filmus, Kawase, Kobayashi &
Yamaguchi, arXiv:1811.09045v3, Lemma 8, proof, p.6). The condition is `f(X + u) = f(X) + f(u)`.

**Formalization Note** The statement is for every set `X` and every representation `w` of `f`, and it
needs no positivity of `f`. -/
theorem lemma_8_oracle_test {E : Type} [DecidableEq E] {k : ℕ} (w : Fin k → E → ℝ)
    (f : Finset E → ℝ) (hw : Represents w f) (X : Finset E) (u : E) (hu : u ∉ X) :
    (f (insert u X) = f X + f {u} ↔
      (activeIndices w f X ∩ activeIndices w f {u}).Nonempty) ∧
    (f (insert u X) = f X + f {u} →
      activeIndices w f (insert u X) = activeIndices w f X ∩ activeIndices w f {u}) := by sorry

end XOSMax
