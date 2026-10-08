-- Prove2me | Definitions.Def_P2MAssembly_Chapter33
-- name    : P2MAssembly_Chapter33
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-09-12T17:02:35.603395+00:00
-- url     : https://prove2.me/theorems/9ced26e2-a009-4bdb-9ace-d4036c41da7a
-- title:
--   Partial Latin arrays, conjugation, and Smetaniuk switching data
-- statement:
--   Write $[n]=\{0,\ldots,n-1\}$ for $n\in\mathbb N$, with $[0]=\varnothing$. A partial array of order $n$ is a map $P:[n]^2\to[n]\cup\{\bot\}$, with $\bot$ denoting an empty cell. Write $F(P)=\{(i,j):P(i,j)\ne\bot\}$ and $U(P)=\{a\in[n]:\exists i,j,\ P(i,j)=a\}$. It is partial Latin when no symbol repeats within a row or column. A completion is a map $L:[n]^2\to[n]$ injective in each row and column, with $L(i,j)=a$ whenever $P(i,j)=a\ne\bot$. For permutations $\rho,\kappa,\sigma$ of $[n]$, put $P^{\rho,\kappa,\sigma}(i,j)=\sigma(P(\rho(i),\kappa(j)))$, where $\sigma(\bot)=\bot$; row and column permutations map new coordinates to old coordinates. For partial Latin $P$, its row-symbol conjugate $P^*$ satisfies $P^*(a,j)=i$ if $P(i,j)=a$, and is empty when no such row exists; column uniqueness makes the row unique. Triangular normalization for a symbol $a$ and position $d$ means that $a$ occurs uniquely at $(d,d)$ and all other filled cells lie strictly above the main diagonal. For $L_0:[N]^2\to[N]$, define $B_{L_0}:[N+1]^2\to[N+1]\cup\{\bot\}$ by
--   $$B_{L_0}(i,j)=\begin{cases}L_0(i,j)&i+j<N,\\N&i+j=N,\\\bot&i+j>N.\end{cases}$$
--    For $P:[N+1]^2\to[N+1]\cup\{\bot\}$, define $Q:[N]^2\to[N]\cup\{\bot\}$ by retaining $P(i,N-j)$ if its value is smaller than $N$, and setting $Q(i,j)=\bot$ otherwise. For $L_0:[N]^2\to[N]$ and $R:[N]\times[N+1]\to[N+1]$, define $\mathcal I_t(L_0,R)$ by these seven conditions: each row of $R$ is injective; each column $j<N$ is injective; column $N$ is injective on rows $i\ge N-t$; $R(i,N)=N$ for $i<N-t$; $R(i,j)=L_0(i,j)$ for $t<j<N$; $R(i,j)=L_0(i,j)$ for $j<N$ and $i+j<N$; and $R(i,N-i)=N$ for $i\ge N-t$. All rows range over $[N]$, and natural-number subtraction is truncated at zero. For $t+1<N$, put $c=t+1$ and $b=N-(t+1)$. Let $T\subseteq[N]$ be the least set containing $b$ and closed under this rule: if $q\in T$, $r\ge b$, and $R(r,N)=R(q,c)$, then $r\in T$. Define $R^{\prime}$ by interchanging columns $c$ and $N$ in each row of $T$, leaving the other entries unchanged. The bundle also defines column-available symbols, used-symbol and used-row sets, row occupancy sets and counts, cyclic Latin squares, cell updates, column reversal, symbol deletion, and full-square conjugation. A partial extension preserves filled cells; a completion additionally supplies a full Latin square. The Evans completion predicate quantifies over partial Latin arrays with at most $\max(n-1,0)$ filled cells; the few-symbol predicate additionally requires $2|U(P)|\le n$.
-- source:
--   Original definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33.lean#L347 (partial arrays and completion); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33.lean#L426 (relabeling); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33Smetaniuk.lean#L17 (symbol occurrence); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33Smetaniuk.lean#L34 (triangular normalization); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33Smetaniuk.lean#L1878 (back-diagonal array); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33Smetaniuk.lean#L2110 (shrink); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33Smetaniuk.lean#L2576 (switching invariant); https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter33Ryser.lean#L203 (row-symbol conjugation). Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 36, “Completing Latin squares”, pp. 253–258 (https://doi.org/10.1007/978-3-662-57265-8_36).

import Init
import Mathlib

/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.Chapter33 -/
section
set_option autoImplicit true

open Finset
open Classical

/-!
# Chapter 33: Completing Latin squares

From "Proofs from THE BOOK":

**Latin square completion**: Any partial Latin square of order n with
at most n-1 entries can be completed to a full Latin square.

The book's proof uses Hall's marriage theorem applied row by row:
at each step, the remaining entries in each row form a system of
distinct representatives.

Point-17 status: this file now contains several genuine pieces: the
row-completion Hall step for a sparse partial square, the state update that
fills an empty row while preserving the partial Latin property and with an
exact filled-cell count, row/column/symbol relabeling infrastructure for the
normalization step in Smetaniuk's exact-cardinality induction, a reduction from
the exact case to a normalized exact case with one prescribed filled cell, the standard
extension of a Latin rectangle by one row, and the padding reduction
`completion_from_exact_cardinality_case`, which proves that the `|P| ≤ n - 1`
case reduces to the exact `|P| = n - 1` Evans case by adding legal entries one
at a time.  The complete completion theorem is also discharged for all partial
squares with at most one filled cell and for orders `0`, `1`, `2`, and `3`.
The canonical `chapter33` theorem is now stated as the full completion theorem
conditional on the exact-cardinality Evans/Smetaniuk case.  It is still not an
unconditional full Evans/Smetaniuk completion theorem.  The
remaining missing infrastructure is the exact-cardinality Smetaniuk induction:
permuting rows/columns/symbols so a singleton symbol lies on the back diagonal
and all other filled cells lie above it, applying the order-`n - 1` induction
hypothesis after deleting that diagonal cell and the last row/column, and
formalizing Smetaniuk's completion of the associated `P(L)` by column
switching.  A direct iteration of `latin_square_completion_step_from_partial`
is not valid after one whole row is added, because the current partial square
then has more than `n - 1` filled cells and the double-counting hypotheses
below no longer describe the enlarged state.

The tempting strengthened row step with fixed entries in the active row also
does not follow from the existing count alone.  After `r` completed rows and
`m = n - r` unfinished rows, Hall for a set `S` of still-empty columns can be
forced by elementary counting in the small range `|S| ≤ m - k` and in the
large range `r < |S|`, where `k` is the number of fixed entries in the active
row.  The middle range `m - k < |S| ≤ r` is exactly where the naive induction
has no contradiction from the available pair counts; this is the point where
the book uses Smetaniuk's diagonal placement and switching construction.  That
switching lemma is the honest remaining frontier for upgrading `chapter33` to
the full completion theorem.
-/

namespace ProofsInTheBook.Chapter33

/-!
### Hall's theorem as the row-by-row engine

The book completes a partial Latin square by repeatedly choosing distinct
representatives from finite availability lists.  The combinatorial engine is
Hall's marriage theorem in exactly this finite-family form.
-/





/-!
### Latin rectangles

The first Hall application in the book says that every `r × n` Latin
rectangle with `r < n` can be extended by one more row.
-/

/-- Symbols missing from column `j` of a Latin rectangle. -/
def rectangleAvailable {r n : ℕ} (R : Fin r → Fin n → Fin n) (j : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun a => ∀ i : Fin r, R i j ≠ a



/-- The column in which row `i` contains symbol `a`. -/
noncomputable def symbolColumn {r n : ℕ} {R : Fin r → Fin n → Fin n}
    (hrow : ∀ i : Fin r, Function.Injective (R i)) (a : Fin n) (i : Fin r) : Fin n :=
  Classical.choose ((hrow i).surjective_of_finite (Equiv.refl (Fin n)) a)









/-!
### Proving Hall's condition from the partial Latin square structure

The premise `hHall_verified` in the Latin square completion step below can be
proved from the partial Latin square structure using double counting.

Key idea: For a set S of columns, let B be the symbols used in every column of S.
Every pair (a, j) with a ∈ B and j ∈ S corresponds to a distinct filled cell.
Since the partial Latin square has at most n-1 filled cells, |B|·|S| ≤ n-1.
If Hall's condition fails (|⋃ available(j)| < |S|), then |B| ≥ n-|S|+1, giving
|B|·|S| ≥ n, a contradiction.
-/











/-!
### Connecting to the partial Latin square representation

A partial Latin square is `P : Fin n → Fin n → Option (Fin n)` where
`P i j = some a` means cell (i,j) contains symbol a, and `P i j = none` means empty.
-/

/-- The set of filled cells of a partial Latin square. -/
def filledCells {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun ij : Fin n × Fin n => (P ij.1 ij.2).isSome

/-- Row and column Latin conditions for a partial square. -/
def IsPartialLatin {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) : Prop :=
  (∀ i j₁ j₂ a, P i j₁ = some a → P i j₂ = some a → j₁ = j₂) ∧
    ∀ i₁ i₂ j a, P i₁ j = some a → P i₂ j = some a → i₁ = i₂

/-- A full Latin square, represented by its value in each cell. -/
def IsLatinSquare {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  (∀ i : Fin n, Function.Injective (L i)) ∧
    ∀ j : Fin n, Function.Injective fun i : Fin n => L i j

/-- A full square completes a partial square if it is Latin and preserves filled cells. -/
def Completes {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (L : Fin n → Fin n → Fin n) : Prop :=
  IsLatinSquare L ∧ ∀ i j a, P i j = some a → L i j = a

/-- The full Evans/Smetaniuk completion theorem for one order. -/
def LatinSquareCompletionTheorem (n : ℕ) : Prop :=
  ∀ P : Fin n → Fin n → Option (Fin n),
    IsPartialLatin P → (filledCells P).card ≤ n - 1 →
      ∃ L : Fin n → Fin n → Fin n, Completes P L

/--
The exact-cardinality case left by the proved padding reduction.  This is the
Smetaniuk switching frontier: once `|P| = n - 1` is completed, the full
`≤ n - 1` theorem follows.
-/
def EvansExactCardinalityCase (n : ℕ) : Prop :=
  ∀ P : Fin n → Fin n → Option (Fin n),
    IsPartialLatin P → (filledCells P).card = n - 1 →
      ∃ L : Fin n → Fin n → Fin n, Completes P L

/-- One partial square extends another when all filled cells are preserved. -/
def ExtendsPartial {n : ℕ} (P Q : Fin n → Fin n → Option (Fin n)) : Prop :=
  ∀ i j a, P i j = some a → Q i j = some a

/-- Symbols already used in row `i`. -/
def rowSymbols {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) (i : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun a => ∃ j, P i j = some a

/-- Symbols already used in column `j`. -/
def colSymbols {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) (j : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun a => ∃ i, P i j = some a

/-- Filled cells in a fixed row. -/
def rowCells {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) (i : Fin n) :
    Finset (Fin n × Fin n) :=
  (filledCells P).filter fun ij => ij.1 = i

/-- Filled cells in a fixed column. -/
def colCells {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) (j : Fin n) :
    Finset (Fin n × Fin n) :=
  (filledCells P).filter fun ij => ij.2 = j

/-- Fill one cell of a partial square, leaving all other cells unchanged. -/
def setCell {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (i₀ j₀ a : Fin n) : Fin n → Fin n → Option (Fin n) :=
  fun i j => if i = i₀ ∧ j = j₀ then some a else P i j





/--
Relabel rows, columns, and symbols of a partial Latin square.

The row and column permutations are read as new-coordinate to old-coordinate
maps, so a filled old cell `(i,j)` appears at
`(rowPerm.symm i, colPerm.symm j)`.
-/
def relabelPartial {n : ℕ} (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    (P : Fin n → Fin n → Option (Fin n)) : Fin n → Fin n → Option (Fin n) :=
  fun i j => Option.map symPerm (P (rowPerm i) (colPerm j))

/-- Relabel rows, columns, and symbols of a full Latin square. -/
def relabelSquare {n : ℕ} (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    (L : Fin n → Fin n → Fin n) : Fin n → Fin n → Fin n :=
  fun i j => symPerm (L (rowPerm i) (colPerm j))









































































/-!
### Elementary complete orders

Squares with at most one filled cell, and orders `0`, `1`, `2`, and `3`, do not
need the Evans/Smetaniuk induction.
-/

/-- The cyclic Latin square on `Fin n`. -/
def cyclicLatinSquare (n : ℕ) : Fin n → Fin n → Fin n := fun i j => i + j



/-- A cyclic Latin square with one prescribed cell value, obtained by a symbol swap. -/
def cyclicLatinSquareWithCell {n : ℕ} (i₀ j₀ a₀ : Fin n) : Fin n → Fin n → Fin n :=
  fun i j => Equiv.swap (i₀ + j₀) a₀ (i + j)













 def latinSquareFinTwoWithCell (i₀ j₀ a₀ : Fin 2) : Fin 2 → Fin 2 → Fin 2 :=
  fun i j =>
    if i = i₀ then
      if j = j₀ then a₀ else Equiv.swap (0 : Fin 2) 1 a₀
    else
      if j = j₀ then Equiv.swap (0 : Fin 2) 1 a₀ else a₀

























/-- The linear Latin squares of order three over `Fin 3`. -/
 def linearLatinFinThree (u v c : Fin 3) : Fin 3 → Fin 3 → Fin 3 :=
  fun i j => u * i + v * j + c



























































end ProofsInTheBook.Chapter33

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter33
-/
/- Source module: ProofsInTheBook.Chapter33Smetaniuk -/
section
set_option autoImplicit true


open Finset
open Classical

namespace ProofsInTheBook.Chapter33

/-!
# Chapter 33: Smetaniuk switching frontier

This file isolates the coordinate bookkeeping for Smetaniuk's normalized
induction.  The hard switching lemma is deliberately left as a named
proposition, not as an unproved theorem.
-/

/-- A symbol occurs in exactly one filled cell. -/
def SymbolOccursExactlyOnce {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (a : Fin n) : Prop :=
  ∃! ij : Fin n × Fin n, P ij.1 ij.2 = some a

/-- All filled cells not using the distinguished symbol lie strictly above the
main diagonal. -/
def StrictUpperTriangle {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (newSym : Fin n) : Prop :=
  ∀ i j s, P i j = some s → s ≠ newSym → i < j

/-- The distinguished symbol occurs exactly once, at the prescribed main
diagonal cell. -/
def MainDiagonalNewSymbol {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (d newSym : Fin n) : Prop :=
  P d d = some newSym ∧ SymbolOccursExactlyOnce P newSym

/-- The strengthened normalized Smetaniuk invariant requested by the handoff. -/
def SmetaniukTriangularNormalized {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (d newSym : Fin n) : Prop :=
  MainDiagonalNewSymbol P d newSym ∧ StrictUpperTriangle P newSym

/-!
## Improper Latin squares

Smetaniuk's induction keeps the order-`N` intermediate square as a signed
array.  A proper cell `[x]` contributes one copy of `x`; an improper cell
`[x+y-z]` contributes `+x + y - z` to every row and column balance, while a
prescribed entry is satisfied by positive syntactic occurrence.
-/

inductive SignedCell (α : Type*) where
  | proper : α → SignedCell α
  | improper : α → α → α → SignedCell α
deriving DecidableEq

namespace SignedCell

variable {α : Type*} [DecidableEq α]



























end SignedCell































































noncomputable def usedSymbols {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun a => ∃ i j, P i j = some a















































 noncomputable def finSuccAboveEquivNe {m : ℕ} (x₀ : Fin (m + 1)) :
    Fin m ≃ {x : Fin (m + 1) // x ≠ x₀} := by
  classical
  refine Equiv.ofBijective (fun i => ⟨x₀.succAbove i, Fin.succAbove_ne x₀ i⟩) ?_
  constructor
  · intro i j hij
    exact x₀.succAbove_right_injective (congrArg Subtype.val hij)
  · intro x
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq x.2
    exact ⟨i, Subtype.ext hi⟩

 noncomputable def splitAt {m : ℕ} (x₀ : Fin (m + 1)) :
    Fin (m + 1) ≃ Option (Fin m) where
  toFun x :=
    if hx : x = x₀ then none else some ((finSuccAboveEquivNe x₀).symm ⟨x, hx⟩)
  invFun o := match o with
    | none => x₀
    | some i => x₀.succAbove i
  left_inv := by
    intro x
    by_cases hx : x = x₀
    · simp [hx]
    · simp [hx]
      exact congrArg Subtype.val ((finSuccAboveEquivNe x₀).apply_symm_apply ⟨x, hx⟩)
  right_inv := by
    intro o
    cases o with
    | none => simp
    | some i =>
        have hne : x₀.succAbove i ≠ x₀ := Fin.succAbove_ne x₀ i
        simp [hne]
        have hsub : (⟨x₀.succAbove i, hne⟩ : {x : Fin (m + 1) // x ≠ x₀}) =
            finSuccAboveEquivNe x₀ i := rfl
        simp [hsub]

 noncomputable def rankLift {m : ℕ} (x₀ : Fin (m + 1))
    (ρ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  (splitAt x₀).trans ((Equiv.optionCongr ρ).trans (finSuccEquiv m).symm)

















/-- Drop the last symbol when passing from order `N + 1` to order `N`. -/
def dropLastSymbol {N : ℕ} (a : Fin (N + 1)) : Option (Fin N) :=
  if h : a.val < N then some ⟨a.val, h⟩ else none





/-- Reverse columns; this is the move from main-diagonal to back-diagonal
coordinates. -/
def reverseColumnsPartial {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) :
    Fin n → Fin n → Option (Fin n) :=
  relabelPartial (Equiv.refl (Fin n)) Fin.revPerm (Equiv.refl (Fin n)) P

















/-!
## Step 1: deletion and shrink in back-diagonal coordinates

For a back-diagonal normalized square `Q`, delete the last row and column `0`.
The retained cell `(i,j)` of the order-`N` problem is `Q i.castSucc j.succ`.
The last symbol is dropped from the symbol type.
-/















/-!
## Smetaniuk's back-diagonal partial square

Given an order-`N` Latin square `L₀`, `smetBackPartial L₀` is the canonical
order-`N + 1` partial square with the new symbol on the back diagonal, `L₀`
below that diagonal, and empty cells above it.
-/

def smetBackPartial {N : ℕ} (L₀ : Fin N → Fin N → Fin N) :
    Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1)) :=
  fun i j =>
    if hdiag : i.val + j.val = N then
      some (Fin.last N)
    else if hlt : i.val + j.val < N then
      some (Fin.castSucc
        (L₀ ⟨i.val, by omega⟩ ⟨j.val, by omega⟩))
    else
      none







def smetMainPartial {N : ℕ} (L₀ : Fin N → Fin N → Fin N) :
    Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1)) :=
  reverseColumnsPartial (smetBackPartial L₀)



















/--
The shrink compatible with `smetMainPartial`: delete the last row and main
column `0`, and reverse the remaining `N` columns.  Thus smaller column `k`
records main column `N - k`, including the original last column as `k = 0`.
-/
def smetMainKeepLastShrink {N : ℕ}
    (P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))) :
    Fin N → Fin N → Option (Fin N) :=
  fun i j => (P (Fin.castSucc i) (Fin.rev (Fin.castSucc j))).bind dropLastSymbol

















/-!
## The Smetaniuk switching rectangle

The core construction first turns the first `N` rows into an `N × (N + 1)`
Latin rectangle.  Column `N` is used as the temporary holding column.  When
processing a column `c`, the active rows are the bottom rows `N - c, …, N - 1`.
Swapping in the first active row puts the new symbol on the back diagonal; if
that creates a repeated old symbol in the holding column, the repair follows
the unique row carrying that old symbol.  The reachable-row closure below
packages exactly that repair chain.
-/

inductive switchReach {N : ℕ}
    (R : Fin N → Fin (N + 1) → Fin (N + 1)) (c : Fin (N + 1))
    (active : Fin N → Prop) (start : Fin N) : Fin N → Prop
  | start : switchReach R c active start start
  | step {q r : Fin N} :
      switchReach R c active start q →
        active r →
          R r (Fin.last N) = R q c →
            switchReach R c active start r







noncomputable def smetSwitchColumn {N : ℕ}
    (R : Fin N → Fin (N + 1) → Fin (N + 1)) (c : Fin (N + 1))
    (active : Fin N → Prop) (start : Fin N) :
    Fin N → Fin (N + 1) → Fin (N + 1) :=
  fun i j =>
    if switchReach R c active start i then
      if j = c then R i (Fin.last N)
      else if j = Fin.last N then R i c
      else R i j
    else R i j









def smetRectInitial {N : ℕ} (L₀ : Fin N → Fin N → Fin N) :
    Fin N → Fin (N + 1) → Fin (N + 1) :=
  fun i j =>
    if h : j.val < N then
      Fin.castSucc (L₀ i ⟨j.val, h⟩)
    else
      Fin.last N





noncomputable def smetRectStep {N : ℕ}
    (R : Fin N → Fin (N + 1) → Fin (N + 1)) (t : ℕ) :
    Fin N → Fin (N + 1) → Fin (N + 1) :=
      if ht : t + 1 < N then
        smetSwitchColumn R ⟨t + 1, by omega⟩
          (fun i : Fin N => N - (t + 1) ≤ i.val)
          ⟨N - (t + 1), by omega⟩
      else
        R

noncomputable def smetRectStage {N : ℕ}
    (L₀ : Fin N → Fin N → Fin N) :
    Nat → Fin N → Fin (N + 1) → Fin (N + 1)
  | 0 => smetRectInitial L₀
  | t + 1 => smetRectStep (smetRectStage L₀ t) t





structure SmetRectStageInvariant {N : ℕ}
    (L₀ : Fin N → Fin N → Fin N) (t : ℕ)
    (R : Fin N → Fin (N + 1) → Fin (N + 1)) : Prop where
  row_inj : ∀ i : Fin N, Function.Injective (R i)
  col_inj : ∀ j : Fin (N + 1), j.val < N →
    Function.Injective fun i : Fin N => R i j
  last_active_inj : ∀ i₁ i₂ : Fin N, N - t ≤ i₁.val → N - t ≤ i₂.val →
    R i₁ (Fin.last N) = R i₂ (Fin.last N) → i₁ = i₂
  last_unactive_new : ∀ i : Fin N, i.val < N - t →
    R i (Fin.last N) = Fin.last N
  unprocessed : ∀ (i : Fin N) (j : Fin (N + 1)) (_htj : t < j.val)
    (hj : j.val < N),
      R i j = Fin.castSucc (L₀ i ⟨j.val, hj⟩)
  required_old : ∀ (i : Fin N) (j : Fin (N + 1)) (hj : j.val < N),
    i.val + j.val < N →
      R i j = Fin.castSucc (L₀ i ⟨j.val, hj⟩)
  diag_active : ∀ i : Fin N, N - t ≤ i.val →
    R i ⟨N - i.val, by omega⟩ = Fin.last N



















def ryser_few_elements_completes (n : ℕ) : Prop :=
  ∀ P : Fin n → Fin n → Option (Fin n),
    IsPartialLatin P → (filledCells P).card ≤ n - 1 →
      2 * (usedSymbols P).card ≤ n →
        ∃ L : Fin n → Fin n → Fin n, Completes P L







end ProofsInTheBook.Chapter33

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter33
-/
/- Source module: ProofsInTheBook.Chapter33Ryser -/
section
set_option autoImplicit true


open Finset
open Classical

namespace ProofsInTheBook.Chapter33

/-!
# Ryser's few-elements case for Chapter 33

This file formalizes the book's Lemma 2 route: first conjugate a partial
Latin square by swapping rows and symbols, then complete a row-sparse partial
square by the row-by-row Hall argument and finish the resulting Latin rectangle.
-/

/-- The symbols that occur in a partial Latin square. -/
def elementsUsed {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun a => ∃ i j, P i j = some a

/-- Rows containing at least one filled cell. -/
def rowsUsed {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ j a, P i j = some a

/-- Number of filled cells in one row. -/
def rowFill {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) (i : Fin n) : ℕ :=
  (rowCells P i).card

/-- Columns filled in one row. -/
def rowFilledCols {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) (i : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun j => (P i j).isSome

/-- Columns empty in one row. -/
def rowEmptyCols {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) (i : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun j => P i j = none

/-- The value in a filled cell, with an arbitrary default on empty cells. -/
noncomputable def cellValue {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (ij : Fin n × Fin n) : Fin n :=
  if h : ∃ a, P ij.1 ij.2 = some a then Classical.choose h else ij.1























/--
The row-symbol conjugate of a partial square: the new row is an old symbol,
the column is unchanged, and the new symbol is the old row.
-/
noncomputable def rowSymbolConjugate {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) : Fin n → Fin n → Option (Fin n) :=
  fun e c =>
    if h : ∃ r, P r c = some e then some (Classical.choose h) else none









/-- Conjugate a full Latin square by swapping rows and symbols. -/
noncomputable def rowSymbolConjugateSquare {n : ℕ}
    (L : Fin n → Fin n → Fin n)
    (hcol : ∀ c : Fin n, Function.Injective fun r : Fin n => L r c) :
    Fin n → Fin n → Fin n :=
  fun a c => Classical.choose ((hcol c).surjective_of_finite (Equiv.refl (Fin n)) a)











def rowsLT (n t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.val < t

def rowsBetween (n lo hi : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => lo < i.val ∧ i.val < hi

def cellsInRows {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (rows : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  rows.biUnion fun i => rowCells P i



























 def ryserStepAvailable {n r t : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (hrn : r ≤ n) (ht : t < r)
    (R : Fin t → Fin n → Fin n)
    (j : {j : Fin n // P (Fin.castLE hrn (⟨t, ht⟩ : Fin r)) j = none}) :
    Finset (Fin n) :=
  let active : Fin n := Fin.castLE hrn (⟨t, ht⟩ : Fin r)
  Finset.univ.filter fun a =>
    a ∉ rowSymbols P active ∧
      (∀ i : Fin t, R i j.1 ≠ a) ∧
      (∀ k : Fin r, t < k.val → P (Fin.castLE hrn k) j.1 ≠ some a)













end ProofsInTheBook.Chapter33

end

/- Original source header (imports hoisted):
/-
Chapter 33 (book chapter 32, "Completing Latin squares"): the unconditional
Evans/Smetaniuk completion theorem.

This file only wires together the two halves proved in
`Chapter33Smetaniuk.lean` (the Smetaniuk singleton-element induction,
following the book proof: normalize the unique symbol onto the diagonal,
delete it, induct, and recover it from the back-diagonal extension) and
`Chapter33Ryser.lean` (book Lemma 2: a sparse partial Latin square using at
most `n / 2` symbols completes, by conjugacy and Hall's theorem).
-/
import ProofsInTheBook.Chapter33Smetaniuk
import ProofsInTheBook.Chapter33Ryser
-/
/- Source module: ProofsInTheBook.Chapter33Unconditional -/
section
set_option autoImplicit true


namespace ProofsInTheBook.Chapter33





end ProofsInTheBook.Chapter33

end


