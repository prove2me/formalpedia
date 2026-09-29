-- Prove2me | Theorems.Thm_hammingDistFn_triangle
-- name    : hammingDistFn_triangle
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:32:57.438989+00:00
-- url     : https://prove2.me/theorems/ffc81233-fc83-4fb5-9d41-ccdce25043e4
-- title:
--   Triangle inequality for Hamming distance: d(u,w) ≤ d(u,v) + d(v,w).
-- statement:
--   Triangle inequality for Hamming distance: d(u,w) ≤ d(u,v) + d(v,w).
--       Bridge: connects metric topology to coding theory.
--       Application: error propagation bounds for compositional post_quantum_security decoders.
--
--   ```lean
--   theorem hammingDistFn_triangle{n : ℕ} {α : Type*} [DecidableEq α]
--       (u v w : Fin n → α) :
--       hammingDistFn u w ≤ hammingDistFn u v + hammingDistFn v w := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/OperadicCodingTheory/HammingMetric.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/OperadicCodingTheory/HammingMetric.lean#L115

-- Thm stub generated from Bridges/OperadicCodingTheory/HammingMetric.lean
import Mathlib
import Definitions.Def_Bridges_OperadicCodingTheory_HammingMetric

/-!
# Hamming Metric for Operadic Coding Theory

Bridge: connects **metric topology** to **information theory** (error-correcting codes).
Application: Hamming distance properties underpin certified robustness bounds for
post-quantum decoding pipelines and neural network verification.

## Main definitions
- `hammingWt`: Hamming weight of a vector (number of nonzero entries)
- `hammingDistFn`: Hamming distance between two vectors
- `LinearCodeParams`: Parameters [n, k, d] of a linear error-correcting code
- `LinearCodeParams.IsMDS`: Predicate characterizing maximum-distance-separable codes

## Main results
- `hammingDistFn_triangle`: Triangle inequality for Hamming distance
- `hammingDistFn_eq_zero`: Identity of indiscernibles
- `singleton_bound_from_params`: The Singleton bound d ≤ n − k + 1
- `mds_error_correction_optimal`: MDS codes have optimal error-correction radius
-/

noncomputable section

/-! ## Section 1: Hamming Weight -/








/-! ## Section 2: Hamming Distance -/

theorem hammingDistFn_triangle{n : ℕ} {α : Type*} [DecidableEq α]
    (u v w : Fin n → α) :
    hammingDistFn u w ≤ hammingDistFn u v + hammingDistFn v w := by sorry
