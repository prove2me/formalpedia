-- Prove2me | Theorems.Thm_Erdos390_column_sparse_floating_rounding
-- name    : Erdos390.column_sparse_floating_rounding
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-16T13:37:12.683767+00:00
-- url     : https://prove2.me/theorems/f5be8c8c-d6eb-4871-9f78-83265bc45a6c
-- title:
--   Floating rounding with exact row sums and bounded column discrepancy
-- statement:
--   Let $A,R,C$ be finite sets, $r:A\to R$ a row assignment, and $I\subseteq C\times A$ a zero-one incidence matrix. Suppose each coordinate belongs to at most $d$ columns. If $x\in[0,1]^A$ has integer sums on every row, there exists $X\in\{0,1\}^A$ such that
--
--   $$\sum_{a:r(a)=s}X_a=\sum_{a:r(a)=s}x_a\quad(s\in R),\qquad \left|\sum_{a:(c,a)\in I}(X_a-x_a)\right|\le 4d\quad(c\in C).$$
--
--   This is the finite rounding step in the guarded upper-bound construction for Erdős problem 390. Its row equalities preserve complete signatures, while its discrepancy bound controls the subsequent prime-valuation correction.
-- source:
--   Shouqiao Wang, A Proposed Solution to Erdos Problem 390, Section 10, Lemma floating-rounding (label lem:floating-rounding); https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/paper.tex ; matching complete Lean proof in 390/lean/Erdos390/WholePaper/FloatingRounding.lean and its four dependencies.

import Definitions.Def_erdos390_floating_rounding
open scoped BigOperators
open Erdos390.WholePaper

theorem Erdos390.column_sparse_floating_rounding
    {A R C : Type*} [Fintype A] [Fintype R] [Fintype C]
    (row : A → R) (inc : C → A → Prop) (d : ℕ) (x : A → ℝ)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hrowInt : ∀ r, ∃ k : ℤ,
      ∑ a ∈ rowSet row r, x a = (k : ℝ))
    (hsparse : ∀ a,
      (columnsContaining Finset.univ inc a).card ≤ d) :
    ∃ X : A → ℝ,
      (∀ a, X a = 0 ∨ X a = 1) ∧
      (∀ r, ∑ a ∈ rowSet row r, X a =
        ∑ a ∈ rowSet row r, x a) ∧
      ∀ c, |∑ a, (X a - x a) * zeroOneColumn inc c a| ≤ (4 * d : ℝ) := by sorry
