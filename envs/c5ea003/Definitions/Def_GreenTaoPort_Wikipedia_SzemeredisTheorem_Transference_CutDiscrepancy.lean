-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:49:56.865097+00:00
-- url     : https://prove2.me/theorems/12ed4d33-bd22-4810-978a-89f3550b0f26
-- title:
--   Cut correlations of functions along the coordinate-sum form
-- statement:
--   A cut-test family has one real function of the other $r-1$ coordinates for each colour of an $r$-tuple. Bounded cut tests take values in $[0,1]$.
--
--   On a finite additive commutative group $G$, the cut correlation of $f-g$ against such a family is
--
--   $$
--   \mathbb E_{x\in G^r}(f-g)\!\left(\sum_i x_i\right)
--   \prod_i u_i(x_{-i}).
--   $$
--
--   Cut discrepancy at most $\varepsilon$ requires the absolute value of every bounded-test correlation to be at most $\varepsilon$. Coordinate deletion and the zero-arity convention are supplied explicitly; no sign or boundedness condition on $f,g$ is part of the predicate.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/CutDiscrepancy.lean#L16-L119

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Cut discrepancy on finite additive groups

This file defines the deletion maps and cut-discrepancy relation used by the
Green--Tao transference argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Delete coordinate `i` from an `r`-tuple. The impossible `r = 0`
case is discharged by eliminating `i : Fin 0`. -/
def eraseCoordinate {G : Type*} {r : ℕ}
    (i : Fin r) (x : Fin r → G) : Fin (r - 1) → G := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ n => exact fun j => x (i.succAbove j)







/-- A family of cut tests, one for each deleted coordinate. -/
abbrev CutTestFamily (G : Type*) (r : ℕ) :=
  (i : Fin r) → (Fin (r - 1) → G) → ℝ

/-- Every member of a cut-test family takes values in `[0,1]`. -/
def IsBoundedCutTest {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) : Prop :=
  (∀ i x, 0 ≤ u i x) ∧ (∀ i x, u i x ≤ 1)

theorem IsBoundedCutTest.nonneg
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) :
    ∀ i x, 0 ≤ u i x :=
  hu.1

theorem IsBoundedCutTest.le_one
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) :
    ∀ i x, u i x ≤ 1 :=
  hu.2

theorem isBoundedCutTest_const
    {G : Type*} {r : ℕ} {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsBoundedCutTest (fun _ : Fin r => fun _ : Fin (r - 1) → G => c) :=
  ⟨fun _ _ => hc0, fun _ _ => hc1⟩



@[simp]
theorem isBoundedCutTest_one
    {G : Type*} {r : ℕ} :
    IsBoundedCutTest
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) :=
  isBoundedCutTest_const (by positivity) le_rfl





/-- The cut correlation of `f-g` with a family of deleted-coordinate
tests. -/
noncomputable def cutCorrelation
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r) : ℝ :=
  mean fun x : Fin r → G =>
    (f (∑ i, x i) - g (∑ i, x i)) *
      ∏ i, u i (eraseCoordinate i x)

/-- `f` and `g` differ by at most `ε` against every product of
`[0,1]`-valued deleted-coordinate tests. -/
def CutDiscrepancyLe
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (ε : ℝ) : Prop :=
  ∀ u : CutTestFamily G r,
    (∀ i x, 0 ≤ u i x) →
    (∀ i x, u i x ≤ 1) →
    |cutCorrelation r f g u| ≤ ε



































end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.cutCorrelation.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


