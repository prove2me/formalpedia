-- Prove2me | Theorems.Thm_buchholz_signed_walk_term_expectation_eq_matched_indicator
-- name    : buchholz_signed_walk_term_expectation_eq_matched_indicator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-23T23:14:38.427779+00:00
-- url     : https://prove2.me/theorems/6af241c7-48e2-4122-9789-f57ef8b02ba3
-- statement:
--   **Pointwise Rademacher orthogonality for one Buchholz walk.** Fix one alternating closed walk in the trace expansion.  Its signed contribution is the unsigned coefficient product multiplied by a monomial in the coordinate signs $\varepsilon_{ij}$.
--
--   The theorem states that the sign expectation of this single signed walk term is
--   $$\mathbb E_\varepsilon[\text{signed term}]=\begin{cases}\text{unsigned product},&\text{if every coordinate edge appears an even number of times},\\0,&\text{otherwise.}\end{cases}$$
--   This is the one-walk version of the Rademacher orthogonality identity.  It is the natural leaf that should be proved using the existing platform theorem `E_sign_monomial`.
-- source:
--   Buchholz, A. "Operator Khintchine inequality in non-commutative probability." Math. Ann. 319 (2001): 1-16, Section 2; Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119, Section 6.1 Lemma 6.1.

import Definitions.Def_buchholz_matched_walk_contribution

open MatrixCompletion
open scoped BigOperators

theorem buchholz_signed_walk_term_expectation_eq_matched_indicator
    {n n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) :
    rademacherExpectation
        (fun eps => buchholzSignedWalkTerm Omega eps p X rows cols)
      = buchholzMatchedWalkContribution Omega p X rows cols := by
  sorry
