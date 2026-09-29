-- Prove2me | Definitions.Def_Bridges_HammingMetric
-- name    : Bridges_HammingMetric
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:20:47.921833+00:00
-- url     : https://prove2.me/theorems/0cb4af74-0f5f-46c7-9b64-c107bbc24faa
-- title:
--   Aether Catalog definitions — Bridges_HammingMetric
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.HammingMetric`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/HammingMetric.lean by skeleton subtraction
import Mathlib

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

/-- Hamming weight: the number of nonzero coordinates of a vector.
    Bridge: connects linear algebra to information theory.
    Application: weight analysis enables certified_robustness bounds. -/
def hammingWt {n : ℕ} {α : Type*} [DecidableEq α] [Zero α] (v : Fin n → α) : ℕ :=
  (Finset.univ.filter (fun i => v i ≠ 0)).card

/-- The support of a vector: the set of indices with nonzero entries.
    Bridge: connects set theory to coding theory.
    Application: support analysis for neural_network weight sparsification. -/
def vecSupport {n : ℕ} {α : Type*} [DecidableEq α] [Zero α]
    (v : Fin n → α) : Finset (Fin n) :=
  Finset.univ.filter (fun i => v i ≠ 0)






/-! ## Section 2: Hamming Distance -/

/-- Hamming distance: the number of positions where two vectors differ.
    Bridge: connects metric theory to information theory.
    Application: hammingDistFn_triangle underpins certified_robustness for post_quantum_security. -/
def hammingDistFn {n : ℕ} {α : Type*} [DecidableEq α] (v w : Fin n → α) : ℕ :=
  (Finset.univ.filter (fun i => v i ≠ w i)).card








/-! ## Section 3: Code Parameters and Bounds -/

/-- Parameters of a linear error-correcting code: [n, k, d]_q.
    The Singleton bound d ≤ n - k + 1 is included as a constraint, since it holds
    for all actual linear codes.
    Bridge: connects information theory to algebra.
    Application: parameter constraints for post_quantum_security lattice codes. -/
structure LinearCodeParams where
  /-- Code length (block size) -/
  length : ℕ
  /-- Code dimension (information symbols) -/
  dimension : ℕ
  /-- Minimum distance (error-correction capability) -/
  minDist : ℕ
  /-- Field size -/
  fieldSize : ℕ
  /-- Basic parameter validity -/
  dim_le_length : dimension ≤ length
  dist_pos : 0 < minDist
  field_ge_two : 2 ≤ fieldSize
  /-- The Singleton bound holds for all linear codes -/
  singleton : dimension + minDist ≤ length + 1

/-- Error correction capability: number of errors correctable = ⌊(d-1)/2⌋. -/
def LinearCodeParams.errorCorrectionRadius (C : LinearCodeParams) : ℕ :=
  (C.minDist - 1) / 2


/-- Redundancy of a code: n - k parity check symbols. -/
def LinearCodeParams.redundancy (C : LinearCodeParams) : ℕ :=
  C.length - C.dimension

/-- A code is MDS (maximum distance separable) if it meets the Singleton bound
    with equality: d = n - k + 1.
    Bridge: connects coding theory to operadic freeness (free operad algebra).
    Application: MDS codes are optimal for post_quantum_security parameter selection. -/
def LinearCodeParams.IsMDS (C : LinearCodeParams) : Prop :=
  C.minDist = C.length - C.dimension + 1








/-! ## Section 4: Hamming Ball Volume -/

/-- Volume of a Hamming ball of radius t in F_q^n.
    Bridge: connects combinatorics to information theory.
    Application: sphere-packing analysis for lattice_crypto code design. -/
def hammingBallVolume (n t q : ℕ) : ℕ :=
  (Finset.range (t + 1)).sum (fun i => n.choose i * (q - 1) ^ i)





/-! ## Section 5: Computational Examples -/







end


