-- Prove2me | Theorems.Thm_Round7DigitLattice_exists_spurious_solution
-- name    : Round7DigitLattice.exists_spurious_solution
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:37:58.540108+00:00
-- url     : https://prove2.me/theorems/b7e1fc72-d714-41f3-8802-9e87c383cafc
-- title:
--   Spurious solutions surround every target.
-- statement:
--   **Spurious solutions surround every target.** For every factorisation target
--   `u ⊗ v` there is a matrix `w` with the *same* digit value (hence a solution of
--   the relaxed system for the same `N`), with **nonzero determinant** — so `w` is
--   not a factorisation — at squared distance at most `8` from the target,
--   independently of the size of `N`.  The relaxed lattice problem therefore cannot
--   isolate the factorisation.
--
--   ```lean
--   theorem Round7DigitLattice.exists_spurious_solution(b : ℤ) (u v : Fin 2 → ℤ) :
--       ∃ w : Matrix (Fin 2) (Fin 2) ℤ,
--         digitVal b w = digitVal b (rankOne u v) ∧ w.det ≠ 0 ∧
--           sqNorm (w - rankOne u v) ≤ 8 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/Round7DigitLattice.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/Round7DigitLattice.lean#L93

-- Thm stub generated from Tropical/Round7DigitLattice.lean
import Mathlib
import Definitions.Def_Tropical_Round7DigitLattice

/-!
# Round-7 closure DIGITLATTICE: the digit-convolution relaxation is not isolated

Experiment 328 linearised the base-`b` digit equations of `N = p q` by setting
`w_{ij} = p_i q_j` and observed that the factorisation target sits *at* the
Gaussian heuristic, so lattice reduction returns generic short vectors instead
of the factorisation.  This file proves the exact structural reason, in the
smallest nontrivial case (two digits per factor), and it is a statement about
*all* `N`, not a heuristic:

* `digitVal_rankOne` : the encoding is faithful — the digit convolution of a
  rank-one matrix `w = u ⊗ v` evaluates to the product of the two numbers
  `u₀ + u₁ b` and `v₀ + v₁ b`.  Factorisations are exactly the rank-one
  solutions.
* `det_rankOne` : rank-one matrices have vanishing determinant; the determinant
  is therefore the obstruction that the linear relaxation throws away.
* `commutator_digitVal` : the "carry commutator" `w = [[0,1],[-1,0]]` lies in the
  kernel of the digit functional for *every* base `b`.  It has squared norm `2`,
  a constant independent of `N`.
* `exists_spurious_solution` : consequently every factorisation target has a
  **non-rank-one companion solution at squared distance at most `8`** — the
  relaxed problem has spurious solutions in an `O(1)` ball around the target,
  whatever the size of `N`.  Since the target's own squared norm grows like the
  product of the digit norms (`sqNorm_rankOne_ge_four` gives the first step),
  short-vector search cannot separate the factorisation from the noise.
-/

open Round7DigitLattice

open Finset

theorem Round7DigitLattice.exists_spurious_solution(b : ℤ) (u v : Fin 2 → ℤ) :
    ∃ w : Matrix (Fin 2) (Fin 2) ℤ,
      digitVal b w = digitVal b (rankOne u v) ∧ w.det ≠ 0 ∧
        sqNorm (w - rankOne u v) ≤ 8 := by sorry
