-- Prove2me | Definitions.Def_EML_AIResearch_EmbeddingTheory
-- name    : EML_AIResearch_EmbeddingTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:20:41.439825+00:00
-- url     : https://prove2.me/theorems/1db04e93-d522-4c7a-9540-4f6b4d3c75bc
-- title:
--   Aether Catalog definitions — EML_AIResearch_EmbeddingTheory
-- statement:
--   Definition bundle for the Aether Catalog module `EML.AIResearch.EmbeddingTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/AIResearch/EmbeddingTheory.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.EML.AIResearch.EmbeddingTheory

Auto-generated from theorem catalog database.
Domain: EML/AIResearch
Declarations: 24
-/

noncomputable section

/-- Standard embedding table: vocab × d_embed -/
def stdEmbeddingTableParams (vocabSize d_embed : ℕ) : ℕ := vocabSize * d_embed

/-- EML factored embedding: vocab × rank + 4 × d_embed.
Cheaper when rank is small relative to d_embed. -/
def emlFactoredEmbeddingParams (vocabSize rank d_embed : ℕ) : ℕ :=
  vocabSize * rank + 4 * d_embed


/-- Standard linear projection: d_in → d_out -/
def stdProjectionParams (d_in d_out : ℕ) : ℕ := d_in * d_out

/-- EML projection: 4 params per output dim -/
def emlProjectionParams (d_out : ℕ) : ℕ := 4 * d_out


/-- Triplet loss: max(0, d(anchor,pos) - d(anchor,neg) + margin) -/
def tripletLoss (d_pos d_neg margin : ℝ) : ℝ := max 0 (d_pos - d_neg + margin)




/-- PCA/projection: reduce d_high to d_low -/
def dimReductionParams (d_high d_low : ℕ) : ℕ := d_high * d_low

/-- EML dimensionality reduction -/
def emlDimReductionParams (d_low : ℕ) : ℕ := 4 * d_low


/-- Memory for quantized embeddings -/
def quantizedEmbeddingMemory (numEmbeddings d_embed bits : ℕ) : ℕ :=
  numEmbeddings * d_embed * bits


/-- Cost of contextual embedding layer (transformer-style) -/
def contextualEmbeddingCost (seqLen d_model : ℕ) : ℕ := seqLen * d_model * d_model

def emlContextualCost (seqLen d_model : ℕ) : ℕ := seqLen * 4 * d_model


/-- Brute-force search cost: compare against all stored embeddings -/
def nnSearchCost (numStored d_embed : ℕ) : ℕ := numStored * d_embed

/-- EML compressed search: lower dimensionality -/
def emlNNSearchCost (numStored d_compressed : ℕ) : ℕ := numStored * d_compressed


/-- Compose two embedding layers -/
def composedEmbeddingParams (d1 d_mid d2 : ℕ) : ℕ := d1 * d_mid + d_mid * d2

/-- EML composed embedding -/
def emlComposedParams (d_mid : ℕ) : ℕ := 4 * d_mid + 4 * d_mid


end


