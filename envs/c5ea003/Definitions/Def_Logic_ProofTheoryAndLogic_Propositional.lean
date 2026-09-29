-- Prove2me | Definitions.Def_Logic_ProofTheoryAndLogic_Propositional
-- name    : Logic_ProofTheoryAndLogic_Propositional
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:02:47.275622+00:00
-- url     : https://prove2.me/theorems/e918f427-02e6-4e35-b8fb-ad8d4e0c1e16
-- title:
--   Aether Catalog definitions — Logic_ProofTheoryAndLogic_Propositional
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.ProofTheoryAndLogic.Propositional`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/ProofTheoryAndLogic/Propositional.lean by skeleton subtraction
import Mathlib

/-! Minimal propositional syntax and semantics used by the proof-refinement development. -/

namespace Logic.Propositional

/-- Propositional formulas over natural-numbered atoms. -/
inductive Formula where
  | atom : ℕ → Formula
  | imp : Formula → Formula → Formula
deriving DecidableEq, Repr

namespace Formula

/-- Evaluation of a formula under a Boolean valuation. -/
def eval (v : ℕ → Bool) : Formula → Bool
  | atom n => v n
  | imp p q => !eval v p || eval v q

/-- Semantic equivalence under every valuation. -/
def SemEq (p q : Formula) : Prop := ∀ v, eval v p = eval v q


end Formula
end Logic.Propositional


