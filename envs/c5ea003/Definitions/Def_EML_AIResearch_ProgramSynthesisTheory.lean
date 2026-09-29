-- Prove2me | Definitions.Def_EML_AIResearch_ProgramSynthesisTheory
-- name    : EML_AIResearch_ProgramSynthesisTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:20:55.352875+00:00
-- url     : https://prove2.me/theorems/2db8905b-6441-4754-9d03-b504988ee90b
-- title:
--   Aether Catalog definitions — EML_AIResearch_ProgramSynthesisTheory
-- statement:
--   Definition bundle for the Aether Catalog module `EML.AIResearch.ProgramSynthesisTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/AIResearch/ProgramSynthesisTheory.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.EML.AIResearch.ProgramSynthesisTheory

Auto-generated from theorem catalog database.
Domain: EML/AIResearch
Declarations: 10
-/

noncomputable section

/-- Cost to generate one code candidate -/
def codeGenCost (modelParams seqLen : ℕ) : ℕ :=
  modelParams * seqLen


/-- Cost of generating N candidates for best-of-N selection -/
def multiCandidateCost (numCandidates genCost : ℕ) : ℕ :=
  numCandidates * genCost



/-- Cost of iterative code refinement: R rounds of generate + test -/
def refinementCost (numRounds genCost testCost : ℕ) : ℕ :=
  numRounds * (genCost + testCost)



/-- Full program synthesis pipeline: generate N candidates, refine top-k -/
def synthPipelineCost (genAllCost refineCost : ℕ) : ℕ :=
  genAllCost + refineCost


end


