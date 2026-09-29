-- Prove2me | Theorems.Thm_HefferonLinAlg_jordanBlocks_unique
-- name    : HefferonLinAlg.jordanBlocks_unique
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T04:01:35.212421+00:00
-- url     : https://prove2.me/theorems/a8dceffe-ce25-4650-a989-968b9e6f24f7
-- title:
--   The Jordan block multiset is an invariant of the matrix
-- statement:
--   Any two Jordan forms of the same square complex matrix have the same multiset of $(\text{block size}, \text{eigenvalue})$ pairs. In other words the Jordan block data is an invariant of the matrix: the blocks may be listed in any order, but which blocks occur, and with what multiplicity, is determined by $A$ alone. This is the uniqueness half of the canonical form, and it is where the difficulty of the goal theorem lives — given it, the goal follows by packaging it with existence.
-- source:
--   Jim Hefferon, *Linear Algebra*, Saint Michael's College, 2020 printing, Chapter Five, Section IV.2, Remark 2.9, printed p. 456, together with Section III.2, Theorem 2.16, printed p. 434

import Mathlib
import Definitions.Def_HefferonLinAlg_jordan

open Matrix

namespace HefferonLinAlg

theorem jordanBlocks_unique
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {k₁ k₂ : ℕ}
    {sz₁ : Fin k₁ → ℕ} {lam₁ : Fin k₁ → ℂ}
    {sz₂ : Fin k₂ → ℕ} {lam₂ : Fin k₂ → ℂ}
    (h₁ : IsJordanFormOf A sz₁ lam₁) (h₂ : IsJordanFormOf A sz₂ lam₂) :
    jordanBlocks sz₁ lam₁ = jordanBlocks sz₂ lam₂ := by
  sorry

end HefferonLinAlg
