-- Prove2me | Theorems.Thm_zero_core_theorem
-- name    : zero_core_theorem
-- status  : Open
-- author  : @@bwdaugherty
-- created : 2026-10-18T10:59:01.573116+00:00
-- url     : https://prove2.me/theorems/b8385b18-db51-4a6c-9c58-4a1523099d62
-- title:
--   Essential Core is Empty for R(5,5) Extension
-- statement:
--   The essential core of the K₄₄ extension problem from the champion R(5,5) coloring is empty: every constraint is necessary, and removing any single constraint leaves the system infeasible.
-- source:
--   Daugherty-Ward-Ryan (2026), DOI: 10.5281/zenodo.19414435

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic

/-- A 2-coloring of K_n edges -/
def Coloring (n : ℕ) := Fin n → Fin n → Bool

/-- Check if all edges in a set have the same color -/
def isMonochromatic {n : ℕ} (χ : Coloring n) (S : Finset (Fin n)) : Prop :=
  (∀ i ∈ S, ∀ j ∈ S, i < j → χ i j = true) ∨
  (∀ i ∈ S, ∀ j ∈ S, i < j → χ i j = false)

/-- A K₄ constraint: 4 vertices forming a monochromatic clique -/
structure K4Constraint where
  vertices : Finset (Fin 43)
  color : Bool
  h_card : vertices.card = 4
deriving BEq

/-- Helper to extend a coloring to K₄₄ -/
def extendColoring (χ₄₃ : Coloring 43) (new_edges : Fin 43 → Bool) : Coloring 44 :=
  fun i j =>
    if hi : i.val < 43 then
      if hj : j.val < 43 then
        χ₄₃ ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else new_edges ⟨i.val, hi⟩
    else
      if hj : j.val < 43 then new_edges ⟨j.val, hj⟩
      else false

/-- A constraint system is feasible if an extension exists that avoids K₅ -/
def feasible (χ : Coloring 43) (constraints : List K4Constraint) : Prop :=
  ∃ (new_edges : Fin 43 → Bool),
    ∀ (S : Finset (Fin 44)), S.card = 5 → ¬isMonochromatic (extendColoring χ new_edges) S

/-- A constraint is essential if removing it makes the system feasible -/
def isEssential (χ : Coloring 43) (cs : List K4Constraint) (c : K4Constraint) : Prop :=
  c ∈ cs ∧ feasible χ (cs.erase c)

/-- The essential core: set of all essential constraints -/
def essentialCore (χ : Coloring 43) (cs : List K4Constraint) : Set K4Constraint :=
  {c | isEssential χ cs c}

/-- Zero-Core Theorem: The essential core of the K₄₄ extension problem
    from the champion R(5,5) coloring is empty. -/
theorem zero_core_theorem :
    ∀ (champion : Coloring 43) (constraints : List K4Constraint),
      constraints.length = 2480 →
      (∀ c ∈ constraints, ¬feasible champion (constraints.erase c)) →
      essentialCore champion constraints = ∅ := by
  sorry
