-- Prove2me | Theorems.Thm_ZamirInversion581_Mult_Supplement_lemma_4_1
-- name    : ZamirInversion581.Mult.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:52:08.413927+00:00
-- url     : https://prove2.me/theorems/be4a7509-d1d7-4fe1-bc80-db1ecce9ba30
-- title:
--   Lemma 4.1 — shift versus uniformity
-- statement:
--   Let $F$ be a finite field of order $q$, let $n\in\mathbb N$, and let $D$ be any randomized map from $n\times n$ matrices to $F$. Put $m=q-1$. Let $P$ be the law of $D(Y)/\det Y$ for uniform invertible $Y$, and $P_A$ the law of $D(RA)/\det R$ for uniform invertible $R$, in both cases with independent algorithm coins. Multiplication by $d\in F^\times$ acts on a law by multiplying its sampled value, leaving zero fixed. Then both assertions hold:
--   $$
--   \det A=d\ne0\ \Longrightarrow\ P_A=dP,\qquad
--   \det A=0\ \Longrightarrow\ \forall z\in F^\times,\ P_A(z)\le1/m.
--   $$
--   The field of two elements is included. This distribution identity and nonzero-atom bound are used in both determinant regimes.
--
--   Differences from the source:
--   - generalization: the normalized-answer law of the determinant algorithm D → an arbitrary randomized map D into PMF F, with no time bound; reason: the probability identity and bound do not use a computation model and include every source algorithm
--   - encoding: nonzero elements and probabilities → units Fˣ and real-valued PMF masses on all of F; reason: unit multiplication fixes zero and every denominator det R is nonzero
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.20, Lemma 4.1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Supplement_Statistics

set_option autoImplicit false

namespace ZamirInversion581.Mult.Supplement

/-- Lemma 4.1, p.20. All randomized maps are allowed, independently of any time bound. -/
theorem lemma_4_1 (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n : ℕ) (D : Mat F n → PMF F) (A : Mat F n) :
    (∀ d : Fˣ, A.det = (d : F) → maskedLaw D A = shift d (normalized D)) ∧
    (A.det = 0 → ∀ z : Fˣ,
      mass (maskedLaw D A) (z : F) ≤ 1 / (Fintype.card F - 1 : ℝ)) := by sorry

end ZamirInversion581.Mult.Supplement
