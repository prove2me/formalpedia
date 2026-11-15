-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearFormsCS
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearFormsCS
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:01:24.263369+00:00
-- url     : https://prove2.me/theorems/671842ec-bc74-4704-a160-1e48e9937f19
-- title:
--   Majorized cut systems and recursive CFZ certificates
-- statement:
--   A majorized cut system has an external parameter, a real core on $n$ coordinates, and nonnegative deleted-coordinate factors bounded by specified majorants. With finite parameter and vertex types, its form is the normalized average of the core times all factors.
--
--   The recursive Cauchy–Schwarz transform removes the head coordinate, stores its two copies in the external parameter, multiplies the remaining factors pairwise, and inserts the head majorant into the new core. The associated recursive-bound predicate caps each paid head-majorant mean and the terminal absolute form.
--
--   A CFZ certificate gives exact identities: each intermediate majorant mean is a Boolean-selected linear-forms average, and the terminal form is a centered face product times a subproduct selecting no forms on that face. The terminal-only certificate retains the last identity while omitting the intermediate ones. These are structural certificates; quantitative estimates are supplied separately.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/WeightedStrongLinearFormsCS.lean#L157-L616

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearForms
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Repeated weighted Cauchy--Schwarz for strong linear forms

This file supplies the recursive analytic bridge which precedes the
algebraic endpoint in `WeightedStrongLinearForms`.

The recursion is the quantitative finite version of Conlon--Fox--Zhao,
Lemma 6.3.  A parameterized cut system consists of a possibly signed core
and one nonnegative factor for every deleted coordinate.  Each factor is
dominated by a designated majorant.  One Cauchy--Schwarz step

* removes the head factor;
* pays the normalized mean of its majorant;
* duplicates the head coordinate;
* pairs every remaining factor; and
* inserts the removed majorant into the new core.

After all coordinates have been processed, the core is the product of all
copies of the original centered factor together with exactly one copy of
each selected face majorant.  No pointwise bound on the majorants is used.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## Weighted finite Cauchy--Schwarz -/









/-! ## Parameterized majorized cut systems -/

/-- A cut system with an external finite parameter space.  The external
parameter records the pairs created by coordinates already processed by
Cauchy--Schwarz. -/
structure MajorizedCutSystem
    (P G : Type*) (n : ℕ) where
  core : P → (Fin n → G) → ℝ
  factor : P → CutTestFamily G n
  majorant : P → CutTestFamily G n
  factor_nonneg :
    ∀ p i x, 0 ≤ factor p i x
  factor_le_majorant :
    ∀ p i x, factor p i x ≤ majorant p i x

namespace MajorizedCutSystem

variable {P G : Type*} {n : ℕ}

/-- Every designated majorant is nonnegative. -/
theorem majorant_nonneg
    (S : MajorizedCutSystem P G n)
    (p : P) (i : Fin n) (x : Fin (n - 1) → G) :
    0 ≤ S.majorant p i x :=
  (S.factor_nonneg p i x).trans
    (S.factor_le_majorant p i x)

/-- The normalized cut expression represented by a system. -/
noncomputable def form
    [Fintype P] [Fintype G]
    (S : MajorizedCutSystem P G n) : ℝ :=
  mean₂ fun p x =>
    S.core p x *
      ∏ i, S.factor p i (eraseCoordinate i x)

/-- The factor left after the head deleted-coordinate factor has been
pulled outside the head-coordinate mean. -/
noncomputable def tailIntegrand
    [Fintype P] [Fintype G]
    (S : MajorizedCutSystem P G (n + 1))
    (p : P) (y : Fin n → G) (a : G) : ℝ :=
  S.core p (Fin.cons a y) *
    ∏ i : Fin n,
      S.factor p i.succ
        (eraseCoordinate i.succ (Fin.cons a y))

/-- The majorant-only moment paid when the head coordinate is removed. -/
noncomputable def headMajorantMean
    [Fintype P] [Fintype G]
    (S : MajorizedCutSystem P G (n + 1)) : ℝ :=
  mean₂ fun p y => S.majorant p 0 y

/-- One recursive weighted Cauchy--Schwarz transform.  The new parameter
contains the two copies of the removed head coordinate. -/
def next
    {n : ℕ}
    (S : MajorizedCutSystem P G (n + 1)) :
    MajorizedCutSystem (P × (G × G)) G n := by
  cases n with
  | zero =>
      exact
        { core := fun q y =>
            S.majorant q.1 0 y *
              S.core q.1 (Fin.cons q.2.1 y) *
              S.core q.1 (Fin.cons q.2.2 y)
          factor := fun _ i => Fin.elim0 i
          majorant := fun _ i => Fin.elim0 i
          factor_nonneg := fun _ i => Fin.elim0 i
          factor_le_majorant := fun _ i => Fin.elim0 i }
  | succ m =>
      exact
        { core := fun q y =>
            S.majorant q.1 0 y *
              S.core q.1 (Fin.cons q.2.1 y) *
              S.core q.1 (Fin.cons q.2.2 y)
          factor := fun q i z =>
            S.factor q.1 i.succ (Fin.cons q.2.1 z) *
              S.factor q.1 i.succ (Fin.cons q.2.2 z)
          majorant := fun q i z =>
            S.majorant q.1 i.succ (Fin.cons q.2.1 z) *
              S.majorant q.1 i.succ (Fin.cons q.2.2 z)
          factor_nonneg := fun q i z =>
            mul_nonneg
              (S.factor_nonneg q.1 i.succ _)
              (S.factor_nonneg q.1 i.succ _)
          factor_le_majorant := fun q i z => by
            exact mul_le_mul
              (S.factor_le_majorant q.1 i.succ _)
              (S.factor_le_majorant q.1 i.succ _)
              (S.factor_nonneg q.1 i.succ _)
              (S.majorant_nonneg q.1 i.succ _) }









/-! ## Quantitative iteration -/





/-- Recursive input for the quantitative CFZ iteration.  At every
successor stage the paid majorant moment is at most `B`; at the
zero-dimensional endpoint the remaining form has absolute value at most
`E`. -/
def HasRecursiveBounds
    {G : Type u} [Fintype G] (B E : ℝ) :
    ∀ {P : Type u} [Fintype P] {n : ℕ},
      MajorizedCutSystem P G n → Prop
  | _, _, 0, S => |S.form| ≤ E
  | _, _, _n + 1, S =>
      S.headMajorantMean ≤ B ∧
        HasRecursiveBounds B E S.next



end MajorizedCutSystem

/-! ## Linear-forms certificates for every paid moment -/



namespace MajorizedCutSystem











/-- A structural certificate that identifies every majorant moment created
by the recursion with an ordinary CFZ linear-forms subproduct and
identifies the final zero-dimensional form with the weighted centered-face
endpoint.

The selector at an intermediate stage is completely arbitrary.  Hence the
certificate supports any mixture of factors bounded by `1` (use the empty
selector) and factors enlarged to their corresponding CFZ majorants. -/
def HasCFZCertificate
    {G : Type u} [Fintype G]
    {k N : ℕ} [NeZero N] (ν : ZMod N → ℝ) (j : Fin k) :
    ∀ {P : Type u} [Fintype P] {n : ℕ},
      MajorizedCutSystem P G n → Prop
  | _, _, 0, S =>
      ∃ other : LinearFormsExponent k,
        (∀ ω, other j ω = false) ∧
          S.form =
            mean (fun x =>
              faceCenteredProduct k N ν j x *
                linearFormsProduct k N ν other x)
  | _, _, _n + 1, S =>
      ∃ e : LinearFormsExponent k,
        S.headMajorantMean =
            mean (linearFormsProduct k N ν e) ∧
          HasCFZCertificate ν j S.next

/-- The terminal-only part of a CFZ certificate.  This is useful for
systems whose majorants are all one, since then every intermediate moment
is discharged automatically by the empty linear-forms selector. -/
def HasCFZTerminal
    {G : Type u} [Fintype G]
    {k N : ℕ} [NeZero N] (ν : ZMod N → ℝ) (j : Fin k) :
    ∀ {P : Type u} [Fintype P] {n : ℕ},
      MajorizedCutSystem P G n → Prop
  | _, _, 0, S =>
      ∃ other : LinearFormsExponent k,
        (∀ ω, other j ω = false) ∧
          S.form =
            mean (fun x =>
              faceCenteredProduct k N ν j x *
                linearFormsProduct k N ν other x)
  | _, _, _n + 1, S =>
      HasCFZTerminal ν j S.next













end MajorizedCutSystem

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.HasRecursiveBounds.eq_1,
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.HasRecursiveBounds.eq_2,
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.HasRecursiveBounds.eq_def,
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.HasRecursiveBounds.match_1,
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.ctorIdx,
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.mk.congr_simp,
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.mk.inj,
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.mk.injEq,
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.next.eq_1,
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.noConfusionType,
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.tailIntegrand.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


