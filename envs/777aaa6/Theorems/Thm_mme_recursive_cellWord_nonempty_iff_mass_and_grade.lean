-- Prove2me | Theorems.Thm_mme_recursive_cellWord_nonempty_iff_mass_and_grade
-- name    : mme_recursive_cellWord_nonempty_iff_mass_and_grade
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T09:52:29.545161+00:00
-- url     : https://prove2.me/theorems/d69b17ae-fa84-40a2-93dd-2b2683da32cb
-- title:
--   Exact feasibility criterion for cell-profile word blocks
-- statement:
--   Let $P$ be a finite set of positions, $W$ a finite set of words, and $c:P\to C$ the cell assignment. Let $g:W\to G$ assign grades, $s:C\to G$ prescribe the cell grades, and $\mu:C\times W\to\mathbb N$ prescribe multiplicities. There exists an assignment $f:P\to W$ satisfying
--
--   $$
--   g(f(p))=s(c(p)),\qquad
--   |\{p:c(p)=d,\ f(p)=w\}|=\mu(d,w)
--   $$
--
--   for every position, cell, and word if and only if
--
--   $$
--   \sum_{w\in W}\mu(d,w)=|c^{-1}(d)|,
--   \qquad
--   \mu(d,w)>0\Longrightarrow g(w)=s(d).
--   $$
--
--   Thus total mass and grade support are the complete combinatorial feasibility conditions for a cell-profile block. No finiteness assumption on the cell or grade sets is required.
-- source:
--   Direct finite histogram realization for RecursiveYZ.CellWord and the mass/reference-target fields of RecursiveYZ.Certificate.Stage.

import Definitions.Def_mme_recursive_yz_stage_certificate
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.BigOperators

open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.Certificate MME.CompleteSplit

theorem mme_recursive_cellWord_nonempty_iff_mass_and_grade
    {P C W G : Type*} [Fintype P] [Fintype W]
    (cell : P → C) (grade : W → G) (shape : C → G) (mu : C → W → ℕ) :
    Nonempty (CellWord cell grade shape mu) ↔
      (∀ c, ∑ w, mu c w = Nat.card {p : P // cell p = c}) ∧
      (∀ c w, 0 < mu c w → grade w = shape c) := by sorry
