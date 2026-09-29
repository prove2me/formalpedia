-- Prove2me | Definitions.Def_Bridges_QuantumSystems_TangledHierarchySoundness
-- name    : Bridges_QuantumSystems_TangledHierarchySoundness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:37:11.534436+00:00
-- url     : https://prove2.me/theorems/6225b680-d79d-4b30-a61b-019db39e8e18
-- title:
--   Aether Catalog definitions — Bridges_QuantumSystems_TangledHierarchySoundness
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.QuantumSystems.TangledHierarchySoundness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/QuantumSystems/TangledHierarchySoundness.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tangled Hierarchies: Proof Systems That Reference Their Own Soundness

This file formalizes *tangled hierarchies* in proof systems — situations where a
system's soundness predicate must appear inside the system it validates. We use
modal fixed-point logics and finite Kripke frames to show such self-reference
is unavoidable.

## Main Results

1. **Iterated soundness depth**: grows linearly with iteration count
2. **Consistency hierarchy**: Con_n formulas have depth exactly n
3. **Entanglement strict growth**: entanglement depth = iteration count
4. **Soundness forces provability**: internalizing soundness with Löb → provability
5. **Diagonal depth bound**: substitution has bounded modal depth increase
6. **Soundness composition**: iterated soundness composes additively
7. **Linear chain characterization**: terminal worlds in linear chains
-/

noncomputable section

open Classical

namespace TangledHierarchy

/-! ## §1. Modal Formulas for Provability Logic -/

/-- Modal formulas for provability logic GL. -/
inductive GLFormula : Type where
  | var : ℕ → GLFormula
  | bot : GLFormula
  | imp : GLFormula → GLFormula → GLFormula
  | box : GLFormula → GLFormula
  deriving Repr, DecidableEq

namespace GLFormula

def neg (φ : GLFormula) : GLFormula := imp φ bot

/-- Modal depth of a formula -/
def modalDepth : GLFormula → ℕ
  | var _ => 0
  | bot => 0
  | imp φ ψ => max (modalDepth φ) (modalDepth ψ)
  | box φ => modalDepth φ + 1

/-- Substitution of ψ for variable n in φ -/
def subst : GLFormula → ℕ → GLFormula → GLFormula
  | .var m, n, ψ => if m = n then ψ else .var m
  | .bot, _, _ => .bot
  | .imp α β, n, ψ => .imp (α.subst n ψ) (β.subst n ψ)
  | .box α, n, ψ => .box (α.subst n ψ)

end GLFormula

/-! ## §2. Kripke Frames for GL -/

/-- A GL-frame: finite, transitive, irreflexive accessibility. -/
structure GLFrame where
  numWorlds : ℕ
  R : Fin numWorlds → Fin numWorlds → Prop
  irrefl : ∀ w, ¬R w w
  trans : ∀ w₁ w₂ w₃, R w₁ w₂ → R w₂ w₃ → R w₁ w₃

def GLValuation (F : GLFrame) := ℕ → Fin F.numWorlds → Prop

/-- Forcing relation: world w forces formula φ under valuation V -/
def forces (F : GLFrame) (V : GLValuation F) : Fin F.numWorlds → GLFormula → Prop
  | w, .var n => V n w
  | _, .bot => False
  | w, .imp φ ψ => forces F V w φ → forces F V w ψ
  | w, .box φ => ∀ w', F.R w w' → forces F V w' φ

def validInFrame (F : GLFrame) (φ : GLFormula) : Prop :=
  ∀ V : GLValuation F, ∀ w : Fin F.numWorlds, forces F V w φ

/-! ## §3. Terminal Worlds -/

def isTerminal (F : GLFrame) (w : Fin F.numWorlds) : Prop :=
  ∀ w', ¬F.R w w'


/-! ## §4. Löb Axiom -/

def loebAxiom (p : ℕ) : GLFormula :=
  .imp (.box (.imp (.box (.var p)) (.var p))) (.box (.var p))

/-
Löb's axiom is valid in all GL-frames.
-/

/-! ## §5. Soundness Operator -/

/-- The soundness operator: □φ → φ -/
def soundnessOp (φ : GLFormula) : GLFormula := .imp (.box φ) φ

/-- Iterated soundness operator -/
def iteratedSoundness : ℕ → GLFormula → GLFormula
  | 0, φ => φ
  | n + 1, φ => soundnessOp (iteratedSoundness n φ)




/-! ## §6. Consistency Hierarchy -/

/-- The n-th consistency formula: Con_0 = ¬⊥, Con_{n+1} = ¬□¬Con_n -/
def conFormula : ℕ → GLFormula
  | 0 => GLFormula.neg .bot
  | n + 1 => GLFormula.neg (.box (GLFormula.neg (conFormula n)))




/-! ## §7. Proof Systems -/

/-- A proof system: set of theorems closed under MP and necessitation -/
structure ProofSystem where
  theorems : Set GLFormula
  mp : ∀ φ ψ, .imp φ ψ ∈ theorems → φ ∈ theorems → ψ ∈ theorems
  nec : ∀ φ, φ ∈ theorems → .box φ ∈ theorems



/-! ## §8. Tangled Proof Algebra -/

/-- A **Tangled Proof Algebra**: finite carrier with box operator.
    This is a novel algebraic structure capturing the essential features
    of self-referential proof systems. -/
structure TangledProofAlgebra where
  carrier : Type
  [fin : Fintype carrier]
  [deceq : DecidableEq carrier]
  box : carrier → carrier
  nontrivial : Fintype.card carrier ≥ 2

attribute [instance] TangledProofAlgebra.fin TangledProofAlgebra.deceq

/-
**Box orbit is bounded** by carrier size (pigeonhole).
-/

/-! ## §9. Entanglement Depth -/

/-- **Entanglement depth**: counts nested □φ → φ patterns. -/
def entanglementDepth : GLFormula → ℕ
  | .var _ => 0
  | .bot => 0
  | .imp (.box φ) ψ =>
    if φ = ψ then entanglementDepth φ + 1
    else max (entanglementDepth (.box φ)) (entanglementDepth ψ)
  | .imp φ ψ => max (entanglementDepth φ) (entanglementDepth ψ)
  | .box φ => entanglementDepth φ



/-! ## §10. Diagonal Depth Bound -/


/-! ## §11. Composition -/



/-! ## §12. Modalized Formulas -/

/-- A formula is modalized in p if every free p is under □ -/
def isModalizedIn : GLFormula → ℕ → Bool
  | .var m, p => m != p
  | .bot, _ => true
  | .imp φ ψ, p => isModalizedIn φ p && isModalizedIn ψ p
  | .box _, _ => true


/-! ## §13. Linear Chain Frames -/

/-- Linear chain frame: world i sees j iff i < j -/
def linearChainFrame (n : ℕ) (_hn : n ≥ 1) : GLFrame where
  numWorlds := n
  R := fun i j => i.val < j.val
  irrefl := fun w h => Nat.lt_irrefl w.val h
  trans := fun _ _ _ h₁ h₂ => Nat.lt_trans h₁ h₂


/-! ## §14. The Reflection Principle -/

def reflectionPrinciple (p : ℕ) : GLFormula := .imp (.box (.var p)) (.var p)


/-! ## §15. Tangled Hierarchy Inevitability -/


/-! ## §16. Witnessing Tangling -/



/-! ## §17. Depth Equality -/



/-! ## §18. Entanglement vs Modal Depth -/


end TangledHierarchy


