-- Prove2me | Definitions.Def_Logic_Propositional
-- name    : Logic_Propositional
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:02:53.951445+00:00
-- url     : https://prove2.me/theorems/a9037e13-1014-423e-a268-caf3a769f8bf
-- title:
--   Aether Catalog definitions — Logic_Propositional
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.Propositional`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/Propositional.lean by skeleton subtraction
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


