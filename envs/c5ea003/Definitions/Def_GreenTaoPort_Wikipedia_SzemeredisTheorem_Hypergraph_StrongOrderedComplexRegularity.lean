-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_StrongOrderedComplexRegularity
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_StrongOrderedComplexRegularity
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:07:22.195219+00:00
-- url     : https://prove2.me/theorems/0f676fbf-5883-4fcd-83d2-f3042a171da2
-- title:
--   Fixed-upper regularity towers and quantitative coarse/fine selections
-- statement:
--   A fixed-budget certificate refines one shared lower layer while holding its upper atom family fixed. It records a number of steps strictly below the budget, preliminary regularity at the given tolerance, and an atom-complexity bound multiplied by $(2^{j+1})^{\text{steps}}$.
--
--   Under nonnegative tolerances and strict energy-budget inequalities, a canonical choice supplies each such certificate. Iterating these choices gives a lower-layer tower and a recursively accumulated complexity factor.
--
--   A fixed-upper coarse/fine selection chooses an index below a positive horizon, with the fine layer refining the coarse layer and the coarse layer refining the input. It records regularity at the selected tolerance, a nonnegative aggregate energy gap at most the upper-face count divided by the horizon, and complexity bounds at the selected index and its successor. Rankwise tolerance selection evaluates each schedule at its chosen index.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/StrongOrderedComplexRegularity.lean#L29-L467

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_BoundaryBernoulli
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Strong coarse/fine regularity for ordered partition complexes

The changing-upper-family obstruction disappears if ranks are selected from
top to bottom.  At rank `j`, freeze the already chosen fine rank-`j+1`
partition and run a long tower of rank-`j` refinements.  An energy
pigeonhole then selects nested coarse/fine rank-`j` partitions with small
energy gap against that fixed upper family.  The fine rank-`j` partition
becomes the frozen target for the next lower rank.

This file first proves the fixed-upper one-rank selector, including fully
precomputed tolerance, budget, and complexity schedules.  It then assembles
those selectors recursively into two ordered partition complexes.  The
resulting fine complex is bounded-test preliminarily regular at every rank,
refines the coarse complex, and has a genuinely small
`totalAtomEnergyGap`: every summand is measured against the corresponding
final fine upper layer.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## One fixed-upper regularity step -/

/-- Output of one fixed-budget lower-layer regularization with its explicit
step count and complexity certificate. -/
structure FixedUpperLayerRegularityCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ)
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (budget : ℕ) where
  steps : ℕ
  fine : OrderedFacePartitionSystem G k j
  steps_lt : steps < budget
  refines : OrderedFacePartitionRefines fine lower
  regular : IsPreliminaryOrderedRegular fine upper ε
  complexity :
    ∀ e,
      FacePartition.complexity (fine e) ≤
        (2 ^ (j + 1)) ^ steps *
          FacePartition.complexity (lower e)

theorem FixedUpperLayerRegularityCertificate.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ} {budget : ℕ}
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (budget : ℝ) * ε ^ 2) :
    Nonempty
      (FixedUpperLayerRegularityCertificate
        G k j lower upper ε budget) := by
  obtain ⟨steps, fine, hsteps, hrefines,
      hregular, hcomplexity⟩ :=
    exists_preliminaryOrderedRegular_refinement_with_complexity_before
      lower upper hε hlong
  exact ⟨{
    steps := steps
    fine := fine
    steps_lt := hsteps
    refines := hrefines
    regular := hregular
    complexity := hcomplexity }⟩

/-- Canonical choice of one fixed-upper lower-layer regularization. -/
noncomputable def chosenFixedUpperLayerRegularityCertificate
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (budget : ℕ)
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (budget : ℝ) * ε ^ 2) :
    FixedUpperLayerRegularityCertificate
      G k j lower upper ε budget :=
  Classical.choice
    (FixedUpperLayerRegularityCertificate.nonempty
      lower upper hε hlong)

/-! ## Canonical fixed-upper tower -/

/-- A lower-layer tower whose upper atom family remains fixed throughout. -/
noncomputable def fixedUpperLayerRegularityTower
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    ℕ → OrderedFacePartitionSystem G k j
  | 0 => initial
  | n + 1 =>
      (chosenFixedUpperLayerRegularityCertificate
        (fixedUpperLayerRegularityTower
          initial upper ε budget hε hlong n)
        upper (ε n) (budget n)
        (hε n) (hlong n)).fine

@[simp]
theorem fixedUpperLayerRegularityTower_zero
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    fixedUpperLayerRegularityTower
      initial upper ε budget hε hlong 0 = initial :=
  rfl

@[simp]
theorem fixedUpperLayerRegularityTower_succ
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (n : ℕ) :
    fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong (n + 1) =
      (chosenFixedUpperLayerRegularityCertificate
        (fixedUpperLayerRegularityTower
          initial upper ε budget hε hlong n)
        upper (ε n) (budget n)
        (hε n) (hlong n)).fine :=
  rfl

/-- Every fixed-upper tower transition refines its predecessor. -/
theorem fixedUpperLayerRegularityTower_refines
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (n : ℕ) :
    OrderedFacePartitionRefines
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong (n + 1))
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong n) := by
  rw [fixedUpperLayerRegularityTower_succ]
  exact
    (chosenFixedUpperLayerRegularityCertificate
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong n)
      upper (ε n) (budget n)
      (hε n) (hlong n)).refines

/-- Every fixed-upper tower stage refines the initial lower layer. -/
theorem fixedUpperLayerRegularityTower_refines_initial
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    ∀ n,
      OrderedFacePartitionRefines
        (fixedUpperLayerRegularityTower
          initial upper ε budget hε hlong n)
        initial := by
  intro n
  induction n with
  | zero =>
      exact OrderedFacePartitionRefines.refl initial
  | succ n ih =>
      exact OrderedFacePartitionRefines.trans
        (fixedUpperLayerRegularityTower_refines
          initial upper ε budget hε hlong n)
        ih

/-- Stage `n+1` is regular for the fixed upper family at tolerance `ε n`. -/
theorem fixedUpperLayerRegularityTower_regular
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (n : ℕ) :
    IsPreliminaryOrderedRegular
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong (n + 1))
      upper (ε n) := by
  rw [fixedUpperLayerRegularityTower_succ]
  exact
    (chosenFixedUpperLayerRegularityCertificate
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong n)
      upper (ε n) (budget n)
      (hε n) (hlong n)).regular

/-- Recursive complexity factor for a fixed-upper rank-`j` tower. -/
def fixedUpperLayerComplexityFactor
    (j : ℕ) (budget : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      (2 ^ (j + 1)) ^ (budget n) *
        fixedUpperLayerComplexityFactor j budget n

/-- Complexity after `n` fixed-upper stages remains ambient-independent. -/
theorem complexity_fixedUpperLayerRegularityTower_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    ∀ (n : ℕ) (e : OrderedFace k j),
      FacePartition.complexity
          (fixedUpperLayerRegularityTower
            initial upper ε budget hε hlong n e) ≤
        fixedUpperLayerComplexityFactor j budget n *
          FacePartition.complexity (initial e) := by
  intro n
  induction n with
  | zero =>
      intro e
      simp [fixedUpperLayerComplexityFactor]
  | succ n ih =>
      intro e
      let certificate :=
        chosenFixedUpperLayerRegularityCertificate
          (fixedUpperLayerRegularityTower
            initial upper ε budget hε hlong n)
          upper (ε n) (budget n)
          (hε n) (hlong n)
      have hstep := certificate.complexity e
      have hexponent :
          (2 ^ (j + 1)) ^ certificate.steps ≤
            (2 ^ (j + 1)) ^ (budget n) :=
        Nat.pow_le_pow_right (by positivity)
          (Nat.le_of_lt certificate.steps_lt)
      rw [fixedUpperLayerRegularityTower_succ]
      calc
        FacePartition.complexity (certificate.fine e) ≤
            (2 ^ (j + 1)) ^ certificate.steps *
              FacePartition.complexity
                (fixedUpperLayerRegularityTower
                  initial upper ε budget hε hlong n e) :=
          hstep
        _ ≤
            (2 ^ (j + 1)) ^ (budget n) *
              FacePartition.complexity
                (fixedUpperLayerRegularityTower
                  initial upper ε budget hε hlong n e) :=
          Nat.mul_le_mul_right _ hexponent
        _ ≤
            (2 ^ (j + 1)) ^ (budget n) *
              (fixedUpperLayerComplexityFactor
                  j budget n *
                FacePartition.complexity (initial e)) :=
          Nat.mul_le_mul_left _ (ih e)
        _ =
            fixedUpperLayerComplexityFactor
                j budget (n + 1) *
              FacePartition.complexity (initial e) := by
          simp [fixedUpperLayerComplexityFactor,
            Nat.mul_assoc]

/-! ## Fixed-upper adjacent selection -/

/-- Selected coarse/fine lower layers for one fixed upper atom family. -/
structure FixedUpperLayerCoarseFine
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ)
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (length : ℕ) where
  index : ℕ
  index_lt : index < length
  coarse : OrderedFacePartitionSystem G k j
  fine : OrderedFacePartitionSystem G k j
  refines : OrderedFacePartitionRefines fine coarse
  coarse_refines_initial :
    OrderedFacePartitionRefines coarse initial
  fine_regular :
    IsPreliminaryOrderedRegular fine upper (ε index)
  gap_nonneg :
    0 ≤ orderedLayerAtomEnergy fine upper -
      orderedLayerAtomEnergy coarse upper
  gap_le :
    orderedLayerAtomEnergy fine upper -
        orderedLayerAtomEnergy coarse upper ≤
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) /
        (length : ℝ)
  coarse_complexity :
    ∀ e,
      FacePartition.complexity (coarse e) ≤
        fixedUpperLayerComplexityFactor
            j budget index *
          FacePartition.complexity (initial e)
  fine_complexity :
    ∀ e,
      FacePartition.complexity (fine e) ≤
        fixedUpperLayerComplexityFactor
            j budget (index + 1) *
          FacePartition.complexity (initial e)

/-- A bounded real sequence has an adjacent increment at most its endpoint
budget divided by the number of transitions. -/
theorem exists_adjacent_real_sub_le_div
    (E : ℕ → ℝ) {length : ℕ}
    (hlength : 0 < length)
    {B : ℝ}
    (hE0 : 0 ≤ E 0)
    (hElast : E length ≤ B) :
    ∃ i : ℕ, i < length ∧
      E (i + 1) - E i ≤ B / length := by
  have htel :
      ∑ i ∈ Finset.range length,
          (E (i + 1) - E i) =
        E length - E 0 :=
    Finset.sum_range_sub E length
  have hsum :
      ∑ i ∈ Finset.range length,
          (E (i + 1) - E i) ≤
        ∑ _i ∈ Finset.range length,
          B / (length : ℝ) := by
    rw [htel]
    calc
      E length - E 0 ≤ B := by linarith
      _ =
          ∑ _i ∈ Finset.range length,
            B / (length : ℝ) := by
        simp only [Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        field_simp
  obtain ⟨i, hi, hsmall⟩ :=
    Finset.exists_le_of_sum_le
      ⟨0, Finset.mem_range.mpr hlength⟩ hsum
  exact ⟨i, Finset.mem_range.mp hi, hsmall⟩

/-- Fixed-upper strong selection at one rank. -/
theorem FixedUpperLayerCoarseFine.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    {length : ℕ} (hlength : 0 < length) :
    Nonempty
      (FixedUpperLayerCoarseFine
        G k j initial upper ε budget length) := by
  let tower :=
    fixedUpperLayerRegularityTower
      initial upper ε budget hε hlong
  obtain ⟨i, hi, hgap⟩ :=
    exists_adjacent_real_sub_le_div
      (fun n => orderedLayerAtomEnergy
        (tower n) upper)
      hlength
      (orderedLayerAtomEnergy_nonneg
        (tower 0) upper)
      (orderedLayerAtomEnergy_le_card
        (tower length) upper)
  refine ⟨{
    index := i
    index_lt := hi
    coarse := tower i
    fine := tower (i + 1)
    refines := ?_
    coarse_refines_initial := ?_
    fine_regular := ?_
    gap_nonneg := ?_
    gap_le := hgap
    coarse_complexity := ?_
    fine_complexity := ?_ }⟩
  · exact fixedUpperLayerRegularityTower_refines
      initial upper ε budget hε hlong i
  · exact fixedUpperLayerRegularityTower_refines_initial
      initial upper ε budget hε hlong i
  · exact fixedUpperLayerRegularityTower_regular
      initial upper ε budget hε hlong i
  · exact sub_nonneg.mpr
      (orderedLayerAtomEnergy_mono
        (fixedUpperLayerRegularityTower_refines
          initial upper ε budget hε hlong i)
        upper)
  · exact complexity_fixedUpperLayerRegularityTower_le
      initial upper ε budget hε hlong i
  · exact complexity_fixedUpperLayerRegularityTower_le
      initial upper ε budget hε hlong (i + 1)

/-- Canonical fixed-upper coarse/fine choice. -/
noncomputable def chosenFixedUpperLayerCoarseFine
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (length : ℕ) (hlength : 0 < length) :
    FixedUpperLayerCoarseFine
      G k j initial upper ε budget length :=
  Classical.choice
    (FixedUpperLayerCoarseFine.nonempty
      initial upper ε budget hε hlong hlength)

/-! ## Top-down all-rank assembly -/

/-- Tolerance selected from the precomputed inner timescale at each rank. -/
def selectedOrderedComplexTolerance
    {r : ℕ}
    (ε : (j : Fin r) → ℕ → ℝ)
    (index : Fin r → ℕ) :
    OrderedRegularityTolerance r :=
  fun j => ε j (index j)



namespace StrongOrderedComplexRegularityCertificate







end StrongOrderedComplexRegularityCertificate

/-! ## Existence by downward rank induction -/



/-! ## Quantitative consequences -/

namespace StrongOrderedComplexRegularityCertificate



















end StrongOrderedComplexRegularityCertificate







end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.FixedUpperLayerCoarseFine.ctorIdx,
    `Wikipedia.SzemeredisTheorem.FixedUpperLayerCoarseFine.mk.inj,
    `Wikipedia.SzemeredisTheorem.FixedUpperLayerCoarseFine.mk.injEq,
    `Wikipedia.SzemeredisTheorem.FixedUpperLayerCoarseFine.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.FixedUpperLayerCoarseFine.noConfusionType,
    `Wikipedia.SzemeredisTheorem.FixedUpperLayerRegularityCertificate.ctorIdx,
    `Wikipedia.SzemeredisTheorem.FixedUpperLayerRegularityCertificate.mk.inj,
    `Wikipedia.SzemeredisTheorem.FixedUpperLayerRegularityCertificate.mk.injEq,
    `Wikipedia.SzemeredisTheorem.FixedUpperLayerRegularityCertificate.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.FixedUpperLayerRegularityCertificate.noConfusionType,
    `Wikipedia.SzemeredisTheorem.fixedUpperLayerComplexityFactor.eq_1,
    `Wikipedia.SzemeredisTheorem.fixedUpperLayerComplexityFactor.eq_2,
    `Wikipedia.SzemeredisTheorem.fixedUpperLayerComplexityFactor.eq_def,
    `Wikipedia.SzemeredisTheorem.fixedUpperLayerRegularityTower.congr_simp,
    `Wikipedia.SzemeredisTheorem.fixedUpperLayerRegularityTower.match_1,
    `Wikipedia.SzemeredisTheorem.selectedOrderedComplexTolerance.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


