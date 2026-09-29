-- Prove2me | Definitions.Def_Bridges_SudokuChromatic
-- name    : Bridges_SudokuChromatic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:18.628551+00:00
-- url     : https://prove2.me/theorems/1e1b136d-9d08-415f-abde-75d92e9145a3
-- title:
--   Aether Catalog definitions — Bridges_SudokuChromatic
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.SudokuChromatic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/SudokuChromatic.lean by skeleton subtraction
import Mathlib

/-!
# A bridge between graph coloring and Sudoku constraint satisfaction

Sudoku on an `n²×n²` grid is a constraint satisfaction problem (CSP): fill each cell with
one of `n²` symbols so that every row, every column and every `n×n` block contains each symbol
exactly once.  Graph coloring is a *different* area of combinatorics: assign colors to the
vertices of a graph so that adjacent vertices receive different colors.

This file makes the classical folklore correspondence **precise and machine-checked**:

* We build the **Sudoku constraint graph** `sudokuGraph n`, whose vertices are the cells and
  whose edges join any two distinct cells that share a row, a column, or a block.
* `isSudokuSolution_iff_properColoring` : a filling is a valid Sudoku solution **iff** it is a
  proper coloring of `sudokuGraph n`.  This is the cross-domain bridge (CSP ↔ graph coloring).
* `sudokuGraph_chromaticNumber` : the **chromatic number** of the Sudoku constraint graph is
  exactly `n²`, the number of symbols.  The lower bound comes from graph theory (a full row is
  a clique of size `n²`), the upper bound from an explicit CSP solution.
* `exists_isSudokuSolution` : every empty `n²×n²` Sudoku is solvable, via an explicit
  arithmetic construction.

The chromatic number being *exactly* `n²` is the graph-theoretic incarnation of the fact that a
Sudoku grid needs, and has enough room for, exactly `n²` symbols — connecting the "critical
number of symbols" of the CSP with a hard graph invariant.
-/

open SimpleGraph

namespace SudokuBridge

/-- The type of cells of an `n²×n²` Sudoku grid. -/
abbrev Cell (n : ℕ) := Fin (n * n) × Fin (n * n)

/-- Two cells are in the same **row**. -/
def sameRow {n : ℕ} (p q : Cell n) : Prop := p.1 = q.1

/-- Two cells are in the same **column**. -/
def sameCol {n : ℕ} (p q : Cell n) : Prop := p.2 = q.2

/-- Two cells are in the same `n×n` **block**. -/
def sameBox {n : ℕ} (p q : Cell n) : Prop :=
  (p.1 : ℕ) / n = (q.1 : ℕ) / n ∧ (p.2 : ℕ) / n = (q.2 : ℕ) / n

/-- The **Sudoku constraint graph**: distinct cells are adjacent iff they lie in a common
row, column, or block. -/
def sudokuGraph (n : ℕ) : SimpleGraph (Cell n) where
  Adj p q := p ≠ q ∧ (sameRow p q ∨ sameCol p q ∨ sameBox p q)
  symm := by
    rintro p q ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr ⟨h.1.symm, h.2.symm⟩)
  loopless := ⟨by rintro p ⟨hne, _⟩; exact hne rfl⟩

/-- A filling `g` of the grid is a **valid Sudoku solution** if no two distinct cells sharing a
row, a column, or a block receive the same symbol. -/
def IsSudokuSolution (n : ℕ) (g : Cell n → Fin (n * n)) : Prop :=
  (∀ p q : Cell n, sameRow p q → p ≠ q → g p ≠ g q) ∧
  (∀ p q : Cell n, sameCol p q → p ≠ q → g p ≠ g q) ∧
  (∀ p q : Cell n, sameBox p q → p ≠ q → g p ≠ g q)

/-! ### The cross-domain bridge -/


/-! ### An explicit Sudoku solution (upper bound on the chromatic number) -/

/-- Explicit value of a completed Sudoku grid at integer coordinates `(r, c)`.
This is the classical "shift" construction `n·(r mod n) + (r div n) + c` reduced mod `n²`. -/
def sudokuVal (n r c : ℕ) : ℕ := (n * (r % n) + r / n + c) % (n * n)

lemma sudokuVal_lt {n : ℕ} (hn : 0 < n) (r c : ℕ) : sudokuVal n r c < n * n :=
  Nat.mod_lt _ (Nat.mul_pos hn hn)









/-- The explicit coloring induced by `sudokuVal`. -/
def sudokuColor (n : ℕ) (hn : 0 < n) (p : Cell n) : Fin (n * n) :=
  ⟨sudokuVal n (p.1 : ℕ) (p.2 : ℕ), sudokuVal_lt hn _ _⟩




/-! ### A full row is a clique (lower bound on the chromatic number) -/

/-- The `n²` cells of the first row, as a finite set. -/
def firstRow (n : ℕ) (hn : 0 < n) : Finset (Cell n) :=
  Finset.univ.image (fun j : Fin (n * n) => (⟨0, Nat.mul_pos hn hn⟩, j))



/-! ### Main result: the chromatic number is exactly `n²` -/


end SudokuBridge


