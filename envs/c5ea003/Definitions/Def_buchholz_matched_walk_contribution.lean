-- Prove2me | Definitions.Def_buchholz_matched_walk_contribution
-- name    : buchholz_matched_walk_contribution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-23T23:13:57.209692+00:00
-- url     : https://prove2.me/theorems/215c8ce1-ff7f-4557-9e26-94aff7181903
-- statement:
--   **One-walk contribution after sign averaging.**
--
--   For a fixed alternating closed row/column walk in the Buchholz trace expansion, this definition returns the unsigned walk product if every coordinate edge has even multiplicity, and returns $0$ otherwise.
--
--   It packages the per-walk right-hand side of the Rademacher orthogonality identity, so the full sign-survival theorem can be written as finite-sum linearity over these one-walk contributions.
-- source:
--   Buchholz, A. "Operator Khintchine inequality in non-commutative probability." Math. Ann. 319 (2001): 1-16, Section 2; Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119, Section 6.1 Lemma 6.1.

import Definitions.Def_buchholz_signed_walk_sum

/-!
One-walk contribution after Rademacher sign averaging.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- The contribution of one walk after sign averaging: unmatched walks
contribute zero; matched walks contribute their unsigned product. -/
noncomputable def buchholzMatchedWalkContribution {n n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2)
    (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) : Real :=
  if buchholzWalkMatched rows cols then
    buchholzWalkProduct Omega p X rows cols
  else
    0

end MatrixCompletion


