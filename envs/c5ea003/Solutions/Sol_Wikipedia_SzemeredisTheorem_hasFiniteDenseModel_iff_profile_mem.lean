-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.hasFiniteDenseModel_iff_profile_mem
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:08:48.476401+00:00
-- url     : https://prove2.me/submissions/0a578bb6-05af-48e6-bf9d-c9a78d06076b

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



/-!
# Finite dense-model duality primitives

The dense-model argument takes place in the finite-dimensional space of
real functions on a finite set.  This file isolates its elementary dual
calculus: normalized pairings, the unit cube, positive parts, and the exact
support function of the unit cube.  In particular, a hyperplane separating
a nonnegative `f ≤ ν` from all `[0,1]`-valued models produces a positive
correlation of `ν - 1` with the positive part of the separator.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped Pointwise







theorem finitePairing_sub_left
    {Ω : Type*} [Fintype Ω]
    (f g q : Ω → ℝ) :
    finitePairing (f - g) q =
      finitePairing f q - finitePairing g q := by
  rw [finitePairing, finitePairing, finitePairing, ← mean_sub]
  apply congrArg mean
  funext x
  simp only [Pi.sub_apply]
  ring











































@[simp]
theorem finiteTestProfile_apply
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (f : Ω → ℝ) (t : τ) :
    finiteTestProfile q f t = finitePairing f (q t) :=
  rfl



theorem mem_profileErrorSet_iff
    {τ : Type*} {ε : ℝ} {e : τ → ℝ} :
    e ∈ profileErrorSet τ ε ↔ ∀ t, |e t| ≤ ε := by
  constructor
  · rintro ⟨hlower, hupper⟩ t
    exact abs_le.mpr ⟨hlower t, hupper t⟩
  · intro h
    exact
      ⟨fun t => (abs_le.mp (h t)).1,
        fun t => (abs_le.mp (h t)).2⟩































































































end Wikipedia.SzemeredisTheorem

end
/-!
# Finite dense-model duality primitives

The dense-model argument takes place in the finite-dimensional space of
real functions on a finite set.  This file isolates its elementary dual
calculus: normalized pairings, the unit cube, positive parts, and the exact
support function of the unit cube.  In particular, a hyperplane separating
a nonnegative `f ≤ ν` from all `[0,1]`-valued models produces a positive
correlation of `ν - 1` with the positive part of the separator.
-/
open Wikipedia.SzemeredisTheorem
open scoped Pointwise

open Wikipedia.SzemeredisTheorem in
/-- Feasibility of the finite dense-model problem is exactly membership of
the target profile in the enlarged profile set. -/
theorem solution
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (f : Ω → ℝ) (ε : ℝ) :
    HasFiniteDenseModel q f ε ↔
      finiteTestProfile q f ∈
        denseModelProfileSet Ω τ q ε := by
  constructor
  · rintro ⟨g, hg, hmatch⟩
    change
      finiteTestProfile q f ∈
        finiteTestProfile q '' unitCubeSet Ω +
          profileErrorSet τ ε
    refine ⟨finiteTestProfile q g, ⟨g, hg, rfl⟩,
      finiteTestProfile q (f - g), ?_, ?_⟩
    · rw [mem_profileErrorSet_iff]
      intro t
      exact hmatch t
    · ext t
      simp only [Pi.add_apply, finiteTestProfile_apply]
      rw [finitePairing_sub_left]
      ring
  · intro hmem
    change
      finiteTestProfile q f ∈
        finiteTestProfile q '' unitCubeSet Ω +
          profileErrorSet τ ε at hmem
    rcases hmem with ⟨p, ⟨g, hg, rfl⟩, e, he, hsum⟩
    refine ⟨g, hg, ?_⟩
    rw [mem_profileErrorSet_iff] at he
    intro t
    have ht := congrFun hsum t
    simp only [Pi.add_apply, finiteTestProfile_apply] at ht
    rw [finitePairing_sub_left]
    rw [← ht]
    simpa using he t
