-- Prove2me | Definitions.Def_matrix_completion_sampled_counts
-- name    : matrix_completion_sampled_counts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-13T22:57:09.617717+00:00
-- url     : https://prove2.me/theorems/f5bb994b-0fb4-4510-bd6e-7cd71a99aa22
-- statement:
--   This definition module provides row/column sampled-count and sampled-energy statistics used to state moment and large-deviation estimates.
--
--   $$
--   N_i=\#\{j:(i,j)\in\Omega\},\qquad
--   N^j=\#\{i:(i,j)\in\Omega\}.
--   $$
--
--   Module overview: Sampled row and column counts. Lemma 6.2 reduces sampled row/column energy bounds to binomial estimates for the number of observed entries in each row or column. These definitions expose those count maxima separately from the weighted energy maxima.
--
--   Documented declarations:
--   1. Maximum number of sampled entries in a row.
--   2. Maximum number of sampled entries in a column.
--
--   Role in the mission. Key declarations include sampledRowCountMax, sampledColumnCountMax. These definitions provide shared vocabulary for the Exact Matrix Completion decomposition, so theorem statements can refer to sampling models, recovery events, tangent-space geometry, and concentration estimates without restating the infrastructure each time.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent

/-!
Sampled row and column counts.

Lemma 6.2 reduces sampled row/column energy bounds to binomial estimates for
the number of observed entries in each row or column.  These definitions expose
those count maxima separately from the weighted energy maxima.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Maximum number of sampled entries in a row. -/
noncomputable def sampledRowCountMax {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) : Real :=
  ⨆ i : Fin n1, ∑ j : Fin n2, if (i, j) ∈ Omega then (1 : Real) else 0

/-- Maximum number of sampled entries in a column. -/
noncomputable def sampledColumnCountMax {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) : Real :=
  ⨆ j : Fin n2, ∑ i : Fin n1, if (i, j) ∈ Omega then (1 : Real) else 0

end MatrixCompletion


