-- Prove2me | Theorems.Thm_trace_pow_reindex
-- name    : trace_pow_reindex
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-25T02:30:41.782413+00:00
-- url     : https://prove2.me/theorems/a82f6531-4e2d-418f-adf3-d5e36b59ffc5
-- statement:
--   **Reindex trace-power invariance.** For a square matrix $M$ over a commutative ring and a bijection $e : m \simeq n$ of finite index types, reindexing commutes with taking powers and traces: $\operatorname{tr}((\operatorname{reindex}_e M)^k) = \operatorname{tr}(M^k)$. This lets a trace-moment inequality proved on one index type (e.g. `Fin d`) be transported to a matrix family on an equivalent index type (e.g. the dilation's `Fin n_1 \oplus Fin n_2`) and pulled back unchanged, since the common cardinality $d$ is preserved. Proof: $(\operatorname{reindex}_e M)^k = \operatorname{reindex}_e (M^k)$ by induction (using `submatrix_mul_equiv`), and trace is invariant under reindexing (sum reindexed by $e$).
-- source:
--   Standard linear algebra (trace and matrix powers are invariant under conjugation by a permutation/reindex). Used to transport a trace-moment engine stated on `Fin d` to a matrix family living on a general finite index (here the Hermitian dilation's index `Fin n1 ⊕ Fin n2`), via an `Equiv`. Candes-Recht 2009 Sec 6.1 application.

import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Reflection
open scoped BigOperators
open Matrix

theorem trace_pow_reindex {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R] (M : Matrix m m R) (e : m ≃ n) (k : ℕ) : Matrix.trace ((M.reindex e e) ^ k) = Matrix.trace (M ^ k) := by sorry
