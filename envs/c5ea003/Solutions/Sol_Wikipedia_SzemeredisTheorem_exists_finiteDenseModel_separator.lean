-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.exists_finiteDenseModel_separator
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:09:56.064938+00:00
-- url     : https://prove2.me/submissions/b61a84aa-373f-42e0-8195-658ae1802a93

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_hasFiniteDenseModel_iff_profile_mem

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



























theorem isUnitBounded_zero {Ω : Type*} :
    IsUnitBounded (fun _ : Ω => (0 : ℝ)) :=
  ⟨fun _ => le_rfl, fun _ => zero_le_one⟩





theorem unitCubeSet_eq_Icc (Ω : Type*) :
    unitCubeSet Ω =
      Set.Icc (fun _ : Ω => (0 : ℝ)) (fun _ => 1) := by
  ext g
  simp [unitCubeSet, IsUnitBounded, Set.mem_Icc, Pi.le_def]

theorem unitCubeSet_convex (Ω : Type*) :
    Convex ℝ (unitCubeSet Ω) := by
  rw [unitCubeSet_eq_Icc]
  exact convex_Icc _ _

theorem unitCubeSet_compact (Ω : Type*) :
    IsCompact (unitCubeSet Ω) := by
  rw [unitCubeSet_eq_Icc]
  exact isCompact_Icc



theorem unitCubeSet_nonempty (Ω : Type*) :
    (unitCubeSet Ω).Nonempty :=
  ⟨fun _ => 0, isUnitBounded_zero⟩













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

theorem profileErrorSet_convex (τ : Type*) (ε : ℝ) :
    Convex ℝ (profileErrorSet τ ε) :=
  convex_Icc _ _

theorem profileErrorSet_compact
    (τ : Type*) (ε : ℝ) :
    IsCompact (profileErrorSet τ ε) :=
  isCompact_Icc



theorem profileErrorSet_nonempty
    (τ : Type*) {ε : ℝ} (hε : 0 ≤ ε) :
    (profileErrorSet τ ε).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  rw [mem_profileErrorSet_iff]
  intro t
  simpa using hε



theorem denseModelProfileSet_convex
    (Ω τ : Type*) [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ε : ℝ) :
    Convex ℝ (denseModelProfileSet Ω τ q ε) := by
  change Convex ℝ
    (finiteTestProfile q '' unitCubeSet Ω +
      profileErrorSet τ ε)
  exact
    (unitCubeSet_convex Ω).linear_image
      (finiteTestProfile q).toLinearMap |>.add
        (profileErrorSet_convex τ ε)

theorem denseModelProfileSet_compact
    (Ω τ : Type*) [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ε : ℝ) :
    IsCompact (denseModelProfileSet Ω τ q ε) := by
  change IsCompact
    (finiteTestProfile q '' unitCubeSet Ω +
      profileErrorSet τ ε)
  exact
    ((unitCubeSet_compact Ω).image
      (finiteTestProfile q).continuous).add
        (profileErrorSet_compact τ ε)

theorem denseModelProfileSet_closed
    (Ω τ : Type*) [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ε : ℝ) :
    IsClosed (denseModelProfileSet Ω τ q ε) :=
  (denseModelProfileSet_compact Ω τ q ε).isClosed

theorem denseModelProfileSet_nonempty
    (Ω τ : Type*) [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (denseModelProfileSet Ω τ q ε).Nonempty :=
  by
    change
      (finiteTestProfile q '' unitCubeSet Ω +
        profileErrorSet τ ε).Nonempty
    exact
      ((unitCubeSet_nonempty Ω).image
        (finiteTestProfile q)).add
          (profileErrorSet_nonempty τ hε)













































































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
/-- Failure of the finite dense-model problem produces a nonzero continuous
linear functional which strictly separates the target profile from every
model profile plus every admissible error vector. -/
theorem solution
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (f : Ω → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfail : ¬HasFiniteDenseModel q f ε) :
    ∃ L : StrongDual ℝ (τ → ℝ), L ≠ 0 ∧
      ∀ (g : Ω → ℝ), IsUnitBounded g →
        ∀ e ∈ profileErrorSet τ ε,
          L (finiteTestProfile q g + e) <
            L (finiteTestProfile q f) := by
  have hnotmem :
      finiteTestProfile q f ∉
        denseModelProfileSet Ω τ q ε := by
    simpa [hasFiniteDenseModel_iff_profile_mem] using hfail
  obtain ⟨L, u, hleft, hright⟩ :=
    geometric_hahn_banach_closed_point
      (denseModelProfileSet_convex Ω τ q ε)
      (denseModelProfileSet_closed Ω τ q ε)
      hnotmem
  have hLne : L ≠ 0 := by
    obtain ⟨s, hs⟩ :=
      denseModelProfileSet_nonempty Ω τ q hε
    intro hzero
    have hslt := hleft s hs
    rw [hzero] at hslt hright
    simp only [ContinuousLinearMap.zero_apply] at hslt hright
    linarith
  refine ⟨L, hLne, ?_⟩
  intro g hg e he
  have hmem :
      finiteTestProfile q g + e ∈
        denseModelProfileSet Ω τ q ε := by
    change
      finiteTestProfile q g + e ∈
        finiteTestProfile q '' unitCubeSet Ω +
          profileErrorSet τ ε
    exact ⟨finiteTestProfile q g, ⟨g, hg, rfl⟩,
      e, he, rfl⟩
  exact (hleft _ hmem).trans hright
