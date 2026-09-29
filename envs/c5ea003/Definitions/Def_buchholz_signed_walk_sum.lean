-- Prove2me | Definitions.Def_buchholz_signed_walk_sum
-- name    : buchholz_signed_walk_sum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-23T23:05:23.379256+00:00
-- url     : https://prove2.me/theorems/de688d99-e6bb-4132-878d-a570d3eee44a
-- statement:
--   **Signed closed-walk sums before sign averaging.**
--
--   This definition module names the raw signed walk expansion that appears before the Rademacher expectation is evaluated.  For each alternating closed walk in the trace expansion of
--   $$(S_\varepsilon S_\varepsilon^{\top})^n,$$
--   it defines the sign monomial contributed by the traversed coordinate edges, the signed walk term, and the signed walk sum $\widetilde W_n(\varepsilon;\Omega,p,X)$.
--
--   Together with `buchholz_walk_sum`, this separates the K-expand algebra from the sign-survival identity: first expand to the signed walk sum, then average signs to obtain the matched-walk sum $W_n(\Omega,p,X)$.
-- source:
--   Buchholz, A. "Operator Khintchine inequality in non-commutative probability." Math. Ann. 319 (2001): 1-16, Section 2; Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119, Section 6.1 Lemma 6.1.

import Definitions.Def_buchholz_walk_sum

/-!
Signed closed-walk sums before the Rademacher average is evaluated.

`buchholzMatchedWalkSum` is the post-expectation object.  The definitions here
name the pre-expectation signed walk expansion, so the K-expand step can be
separated from the sign-orthogonality step.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- The Rademacher sign monomial attached to an alternating closed walk. -/
noncomputable def buchholzWalkSignMonomial {n n1 n2 : Nat}
    (eps : Finset (Fin n1 × Fin n2))
    (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) : Real :=
  ∏ k : Fin n,
    (rademacherSign eps (rows k) (cols k) *
      rademacherSign eps (rows (buchholzCyclicSucc k)) (cols k))

/-- One signed walk contribution in the trace expansion of
`(Sε * Sεᵀ)^n`. -/
noncomputable def buchholzSignedWalkTerm {n n1 n2 : Nat}
    (Omega eps : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2)
    (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) : Real :=
  buchholzWalkProduct Omega p X rows cols *
    buchholzWalkSignMonomial eps rows cols

/-- The raw signed closed-walk expansion before averaging over the sign cube. -/
noncomputable def buchholzSignedWalkSum {n1 n2 : Nat}
    (n : Nat) (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) (eps : Finset (Fin n1 × Fin n2)) : Real :=
  ∑ rows : Fin n → Fin n1,
    ∑ cols : Fin n → Fin n2,
      buchholzSignedWalkTerm Omega eps p X rows cols

end MatrixCompletion


