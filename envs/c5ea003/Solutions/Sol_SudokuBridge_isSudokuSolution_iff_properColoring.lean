-- Prove2me | solution 1 for SudokuBridge.isSudokuSolution_iff_properColoring
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:57:43.19385+00:00
-- url     : https://prove2.me/submissions/df81422c-d8e5-44db-ac93-c8bcd69a0cc4

-- Sol generated from Bridges/SudokuChromatic.lean
import Mathlib
import Definitions.Def_Bridges_SudokuChromatic

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

open SudokuBridge







/-! ### The cross-domain bridge -/


/-! ### An explicit Sudoku solution (upper bound on the chromatic number) -/















/-! ### A full row is a clique (lower bound on the chromatic number) -/




/-! ### Main result: the chromatic number is exactly `n²` -/



open SudokuBridge in
theorem solution{n : ℕ} (g : Cell n → Fin (n * n)) :
    IsSudokuSolution n g ↔ ∀ p q : Cell n, (sudokuGraph n).Adj p q → g p ≠ g q := by
  constructor
  · rintro ⟨hrow, hcol, hbox⟩ p q ⟨hne, hor⟩
    rcases hor with h | h | h
    · exact hrow p q h hne
    · exact hcol p q h hne
    · exact hbox p q h hne
  · intro H
    refine ⟨?_, ?_, ?_⟩
    · intro p q hs hne; exact H p q ⟨hne, Or.inl hs⟩
    · intro p q hs hne; exact H p q ⟨hne, Or.inr (Or.inl hs)⟩
    · intro p q hs hne; exact H p q ⟨hne, Or.inr (Or.inr hs)⟩
