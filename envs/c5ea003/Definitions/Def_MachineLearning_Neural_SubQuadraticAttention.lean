-- Prove2me | Definitions.Def_MachineLearning_Neural_SubQuadraticAttention
-- name    : MachineLearning_Neural_SubQuadraticAttention
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:47:51.00998+00:00
-- url     : https://prove2.me/theorems/40863507-34ae-4594-938f-aa78fc8569d1
-- title:
--   Aether Catalog definitions — MachineLearning_Neural_SubQuadraticAttention
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.Neural.SubQuadraticAttention`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/Neural/SubQuadraticAttention.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.MachineLearning.Neural.SubQuadraticAttention

Auto-generated from theorem catalog database.
Domain: MachineLearning/Neural
Declarations: 16
-/


noncomputable section

/-- The block size for sub-quadratic attention: B = max(⌈√N⌉, 1). -/
def blockSize (N : ℕ) : ℕ := max (Nat.sqrt N + 1) 1






/-- The block index of token i. -/
def blockIndex (N : ℕ) (i : ℕ) : ℕ := i / blockSize N


/-- The sparse attention mask: token i attends to token j iff they are
in the same block, or j is in block 0 (the global anchor block). -/
def sparseAttentionMask (N : ℕ) (i j : ℕ) : Bool :=
  (blockIndex N i = blockIndex N j) || (blockIndex N j = 0)


/-- Number of tokens that token i attends to under block-sparse attention. -/
def sparseAttendCount (N : ℕ) (i : ℕ) : ℕ :=
  ((Finset.range N).filter (fun j => sparseAttentionMask N i j = true)).card


/-- The total number of attention pairs in full quadratic attention. -/
def fullAttentionPairs (N : ℕ) : ℕ := N * N


/-- The total number of attention pairs in block-sparse attention. -/
def sparseAttentionPairs (N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range N, sparseAttendCount N i










/-- Frobenius norm squared of a matrix. -/
def frobeniusNormSq (n m : ℕ) (M : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin m, (M i j) ^ 2




/-- The residual (error) matrix from masking. -/
def maskResidual (n : ℕ) (mask : Fin n → Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => if mask i j then 0 else M i j)




end


