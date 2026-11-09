-- Prove2me | Definitions.Def_Couret_RecohParityGenerator_deb90a4bb68d
-- name    : Couret_RecohParityGenerator_deb90a4bb68d
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:11:00.937685+00:00
-- url     : https://prove2.me/theorems/cd9ed8fd-fd53-4710-a915-4b1d59500255
-- title:
--   Parity-based representatives of triple square fibres
-- statement:
--   Defines the odd part of a sparse square profile, its halved even residual, normalization around a candidate doubled point, and guarded constructions of representative triples using a supplied partial halving solver. The final representative set filters for size three and the exact square check. Defines a cover contract requiring all representatives to realize the observed square and every realizing triple to be a two-torsion translate of one.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParityGenerator.lean; source file SHA-256 c0de570c34b3a0044573486512e463147ffae9acc9eff636411cbf33711eee31

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohSquareSelector_3b7a2954c02a

set_option autoImplicit false
set_option maxRecDepth 2000

/-!
The compact parity generator for three-point ordered squares.

All executable searches are over the supplied finite square support U,
one residual set, or its two-element subsets. There is no `Fintype G`
assumption on the generator. The final exact-square test is performed after
the chosen translation; the translation identity below relates it to the
normalized square test used by Python v0.2.

This module proves a mathematical coverage contract for these Lean
definitions. It does not provide a semantics for Python, JSON or its runtime.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Natural-valued indicator, used only on finite supplied sets. -/
def recohParityIndicator (A : Finset G) (z : G) : ℕ :=
  if z ∈ A then 1 else 0

/-- Positions with odd coefficients, found inside the supplied support. -/
def recohParityOddSupport (U : Finset G) (R : G → ℕ) : Finset G :=
  U.filter (fun z => R z % 2 = 1)

/-- Residual after deleting the odd diagonal contributions. -/
def recohParityEdgeResidual (U : Finset G) (R : G → ℕ) (z : G) : ℕ :=
  (R z - recohParityIndicator (recohParityOddSupport U R) z) / 2

def recohParityEdges (U : Finset G) (R : G → ℕ) : Finset G :=
  U.filter (fun z => 0 < recohParityEdgeResidual U R z)

/-- An exact guard for the residual being an indicator. The equation also
checks nonnegative subtraction and divisibility by two. -/
def recohParityEdgeGuard (U : Finset G) (R : G → ℕ) : Prop :=
  ∀ z ∈ U, R z = recohParityIndicator (recohParityOddSupport U R) z +
    2 * recohParityIndicator (recohParityEdges U R) z

instance (U : Finset G) (R : G → ℕ) : Decidable (recohParityEdgeGuard U R) :=
  inferInstanceAs (Decidable (∀ z ∈ U, R z =
    recohParityIndicator (recohParityOddSupport U R) z +
      2 * recohParityIndicator (recohParityEdges U R) z))

def recohParityNormalizedSupport (U : Finset G) (d : G) : Finset G :=
  U.image (fun z => z - d)

def recohParitySingleResidual (R : G → ℕ) (d z : G) : ℕ :=
  (R (z + d) - recohParityIndicator ({0} : Finset G) z) / 2

def recohParityQuad (U : Finset G) (R : G → ℕ) (d : G) : Finset G :=
  (recohParityNormalizedSupport U d).filter
    (fun z => 0 < recohParitySingleResidual R d z)

def recohParitySingleGuard (U : Finset G) (R : G → ℕ) (d : G) : Prop :=
  ∀ z ∈ recohParityNormalizedSupport U d,
    R (z + d) = recohParityIndicator ({0} : Finset G) z +
      2 * recohParityIndicator (recohParityQuad U R d) z

instance (U : Finset G) (R : G → ℕ) (d : G) :
    Decidable (recohParitySingleGuard U R d) :=
  inferInstanceAs (Decidable (∀ z ∈ recohParityNormalizedSupport U d,
    R (z + d) = recohParityIndicator ({0} : Finset G) z +
      2 * recohParityIndicator (recohParityQuad U R d) z))

/-- All admissible two-point choices from the four-point residual. -/
def recohParityLocalPairs (Q : Finset G) : Finset (Finset G) :=
  (Q.powersetCard 2).filter (fun P =>
    0 ∉ P ∧ ∀ a ∈ P, ∀ b ∈ P, a + a = b + b)

/-- Single-odd branch. Since its caller supplies a singleton odd support,
there is exactly one possible d; no arbitrary ambient choice is made. -/
def recohParitySingleSeeds (U : Finset G) (R : G → ℕ)
    (half : G → Option G) (d : G) : Finset (Finset G) :=
  if (recohParityQuad U R d).card = 4 ∧ recohParitySingleGuard U R d then
    match half d with
    | none => ∅
    | some c => (recohParityLocalPairs (recohParityQuad U R d)).image
        (fun P => translateSupport (insert 0 P) c)
  else ∅

/-- Raw compact family before the independent exact-square check. -/
def recohParityRawSeeds (U : Finset G) (R : G → ℕ)
    (half : G → Option G) : Finset (Finset G) :=
  if (recohParityOddSupport U R).card = 3 then
    if (recohParityEdges U R).card = 3 ∧ recohParityEdgeGuard U R then
      match half ((recohParityEdges U R).sum id) with
      | none => ∅
      | some sigma => {recohEdgeDecode (recohParityEdges U R) sigma}
    else ∅
  else if (recohParityOddSupport U R).card = 1 then
    (recohParityOddSupport U R).biUnion (recohParitySingleSeeds U R half)
  else ∅

/-- Compact representatives, before removing equivalent two-torsion orbits. -/
def recohParityRepresentatives (U : Finset G) (R : G → ℕ)
    (half : G → Option G) : Finset (Finset G) :=
  (recohParityRawSeeds U R half).filter
    (fun B => B.card = 3 ∧ recohSparseSquareCheck U B R = true)

/-- The semantic contract is coverage of orbits, not equality of lists. -/
def RecohParityCover (R : G → ℕ) (reps : Finset (Finset G)) : Prop :=
  (∀ B ∈ reps, B.card = 3 ∧ orderedSquare B = R) ∧
  (∀ S : Finset G, S.card = 3 → orderedSquare S = R →
    ∃ B ∈ reps, OrdinaryPartner B S)

theorem recoh_parity_representatives_sound
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (hR : ∀ z, R z ≠ 0 → z ∈ U)
    (B : Finset G) (hB : B ∈ recohParityRepresentatives U R half) :
    B.card = 3 ∧ orderedSquare B = R := by
  obtain ⟨_, hcard, hcheck⟩ := Finset.mem_filter.mp hB
  exact ⟨hcard, (recoh_sparse_square_check_iff U B R hR).mp hcheck⟩

/-- Exact shift identity, including every diagonal contribution. -/
theorem recoh_ordered_square_translate_shift (B : Finset G) (u z : G) :
    orderedSquare (translateSupport B u) (z + (u + u)) = orderedSquare B z := by
  have hinj : ∀ x ∈ B, ∀ y ∈ B, (fun a : G => a + u) x =
      (fun a : G => a + u) y → x = y :=
    fun _ _ _ _ h => add_right_cancel h
  unfold orderedSquare translateSupport
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro y _
  have he : (x + u) + (y + u) = z + (u + u) ↔ x + y = z := by
    have hx : (x + u) + (y + u) = (x + y) + (u + u) := by abel
    rw [hx, add_right_cancel_iff]
  simp only [he]



omit [AddCommGroup G] in
private theorem parity_indicator_three (a b c z : G)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (if a = z then 1 else 0) + (if b = z then 1 else 0) +
      (if c = z then 1 else 0) =
      recohParityIndicator ({a, b, c} : Finset G) z := by
  simp only [recohParityIndicator, Finset.mem_insert, Finset.mem_singleton]
  split_ifs <;> aesop

omit [AddCommGroup G] in
private theorem parity_indicator_four (a b c d z : G)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (if a = z then 1 else 0) + (if b = z then 1 else 0) +
      (if c = z then 1 else 0) + (if d = z then 1 else 0) =
      recohParityIndicator ({a, b, c, d} : Finset G) z := by
  simp only [recohParityIndicator, Finset.mem_insert, Finset.mem_singleton]
  split_ifs <;> aesop

omit [AddCommGroup G] in
private theorem parity_odd_eq_of_expansion (U D E : Finset G) (R : G → ℕ)
    (hD : D ⊆ U)
    (hexp : ∀ z, R z = recohParityIndicator D z + 2 * recohParityIndicator E z) :
    recohParityOddSupport U R = D := by
  ext z
  simp only [recohParityOddSupport, Finset.mem_filter]
  rw [hexp z]
  by_cases hz : z ∈ D
  · have hu := hD hz
    by_cases he : z ∈ E <;> simp [recohParityIndicator, hz, hu, he]
  · by_cases he : z ∈ E <;> simp [recohParityIndicator, hz, he]

omit [AddCommGroup G] in
private theorem parity_edges_eq_of_expansion (U D E : Finset G) (R : G → ℕ)
    (hD : D ⊆ U) (hE : E ⊆ U)
    (hexp : ∀ z, R z = recohParityIndicator D z + 2 * recohParityIndicator E z) :
    recohParityEdges U R = E := by
  have hodd := parity_odd_eq_of_expansion U D E R hD hexp
  ext z
  simp only [recohParityEdges, Finset.mem_filter, recohParityEdgeResidual, hodd]
  rw [hexp z]
  by_cases hz : z ∈ E
  · have hu := hE hz
    simp [recohParityIndicator, hz, hu]
  · simp [recohParityIndicator, hz]

omit [AddCommGroup G] in
private theorem parity_edge_guard_of_expansion (U D E : Finset G) (R : G → ℕ)
    (hD : D ⊆ U) (hE : E ⊆ U)
    (hexp : ∀ z, R z = recohParityIndicator D z + 2 * recohParityIndicator E z) :
    recohParityEdgeGuard U R := by
  intro z _
  rw [parity_odd_eq_of_expansion U D E R hD hexp,
    parity_edges_eq_of_expansion U D E R hD hE hexp]
  exact hexp z

private theorem parity_normalized_support_covered (U : Finset G) (R : G → ℕ)
    (hR : ∀ z, R z ≠ 0 → z ∈ U) (d z : G) (hz : R (z + d) ≠ 0) :
    z ∈ recohParityNormalizedSupport U d := by
  exact Finset.mem_image.mpr ⟨z + d, hR _ hz, by abel⟩

private theorem parity_quad_eq_of_expansion (U Q : Finset G) (R : G → ℕ)
    (hR : ∀ z, R z ≠ 0 → z ∈ U) (d : G)
    (hexp : ∀ z, R (z + d) = recohParityIndicator ({0} : Finset G) z +
      2 * recohParityIndicator Q z) :
    recohParityQuad U R d = Q := by
  ext z
  simp only [recohParityQuad, Finset.mem_filter, recohParitySingleResidual]
  rw [hexp z]
  by_cases hz : z ∈ Q
  · have hp : R (z + d) ≠ 0 := by
      rw [hexp z]
      simp [recohParityIndicator, hz]
    have hu := parity_normalized_support_covered U R hR d z hp
    simp [recohParityIndicator, hz, hu]
  · simp [recohParityIndicator, hz]

private theorem parity_single_guard_of_expansion (U Q : Finset G) (R : G → ℕ)
    (hR : ∀ z, R z ≠ 0 → z ∈ U) (d : G)
    (hexp : ∀ z, R (z + d) = recohParityIndicator ({0} : Finset G) z +
      2 * recohParityIndicator Q z) :
    recohParitySingleGuard U R d := by
  intro z _
  rw [parity_quad_eq_of_expansion U Q R hR d hexp]
  exact hexp z

omit [AddCommGroup G] in
private theorem parity_odd_eq_singleton (U : Finset G) (R : G → ℕ)
    (hR : ∀ z, R z ≠ 0 → z ∈ U) (d : G)
    (hp : ∀ z, R z % 2 = if d = z then 1 else 0) :
    recohParityOddSupport U R = {d} := by
  ext z
  simp only [recohParityOddSupport, Finset.mem_filter, Finset.mem_singleton]
  rw [hp z]
  by_cases hz : z = d
  · subst z
    have hu : d ∈ U := hR d (by intro h; have hh := hp d; simp [h] at hh)
    simp [hu]
  · simp [hz, Ne.symm hz]

private theorem parity_quad_expansion (a b : G)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (hdouble : a + a = b + b) :
    ({a + a, a, b, a + b} : Finset G).card = 4 ∧
    ∀ z, orderedSquare ({0, a, b} : Finset G) z =
      recohParityIndicator ({0} : Finset G) z +
        2 * recohParityIndicator ({a + a, a, b, a + b} : Finset G) z := by
  have hAa : a + a ≠ a := by
    intro h
    exact ha (add_left_cancel (show a + a = a + 0 by simpa using h))
  have hAb : a + a ≠ b := by
    intro h
    have hh : b + b = b := hdouble.symm.trans h
    exact hb (add_left_cancel (show b + b = b + 0 by simpa using hh))
  have hAab : a + a ≠ a + b := fun h => hab (add_left_cancel h)
  have haab : a ≠ a + b := by
    intro h
    exact hb (add_left_cancel (show a + b = a + 0 by simpa using h.symm))
  have hbab : b ≠ a + b := by
    intro h
    exact ha (add_right_cancel (show a + b = 0 + b by simpa using h.symm))
  constructor
  · simp [hAa, hAb, hAab, hab, haab, hbab]
  · intro z
    have hi := parity_indicator_four (a + a) a b (a + b) z
      hAa hAb hAab hab haab hbab
    have h0 : recohParityIndicator ({0} : Finset G) z =
        (if (0 : G) = z then 1 else 0) := by
      simp [recohParityIndicator, eq_comm]
    rw [orderedSquare_three 0 a b z (Ne.symm ha) (Ne.symm hb) hab, h0]
    simp only [tripleSquareCoeff, diagCoeff, offCoeff, zero_add, ← hdouble]
    omega

/-- The three-odd branch covers every triple with distinct doubling values.
The residual's shape and the cardinal guards are proved from the square. -/
theorem recoh_parity_complete_distinct
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (hhalf : RecohHalfSolverSpec half) (hR : ∀ z, R z ≠ 0 → z ∈ U)
    (a b c : G) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hab2 : a + a ≠ b + b) (hac2 : a + a ≠ c + c) (hbc2 : b + b ≠ c + c)
    (hsquare : orderedSquare ({a, b, c} : Finset G) = R) :
    ∃ B ∈ recohParityRepresentatives U R half,
      OrdinaryPartner B ({a, b, c} : Finset G) := by
  let D : Finset G := {a + a, b + b, c + c}
  let E : Finset G := {a + b, a + c, b + c}
  have he12 : a + b ≠ a + c := fun h => hbc (add_left_cancel h)
  have he13 : a + b ≠ b + c := by
    intro h
    exact hac (add_right_cancel (show a + b = c + b by simpa [add_comm] using h))
  have he23 : a + c ≠ b + c := fun h => hab (add_right_cancel h)
  have hexp : ∀ z, R z = recohParityIndicator D z + 2 * recohParityIndicator E z := by
    intro z
    rw [← hsquare, orderedSquare_three a b c z hab hac hbc]
    unfold tripleSquareCoeff diagCoeff offCoeff
    rw [parity_indicator_three (a + a) (b + b) (c + c) z hab2 hac2 hbc2,
      parity_indicator_three (a + b) (a + c) (b + c) z he12 he13 he23]
  have hDU : D ⊆ U := by
    intro z hz
    apply hR z
    rw [hexp z]
    simp [recohParityIndicator, hz]
  have hEU : E ⊆ U := by
    intro z hz
    apply hR z
    rw [hexp z]
    simp [recohParityIndicator, hz]
  have hodd := parity_odd_eq_of_expansion U D E R hDU hexp
  have hedges := parity_edges_eq_of_expansion U D E R hDU hEU hexp
  have hguard := parity_edge_guard_of_expansion U D E R hDU hEU hexp
  have hDcard : D.card = 3 := by simp [D, hab2, hac2, hbc2]
  have hEcard : E.card = 3 := by simp [E, he12, he13, he23]
  have hsum : (a + b + c) + (a + b + c) = E.sum id := by
    simp only [E, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      not_or, he12, he13, he23, not_false_eq_true, and_self,
      Finset.sum_singleton, id_eq]
    abel
  obtain ⟨sigma0, hsigma0⟩ := hhalf.2 (E.sum id) ⟨a + b + c, hsum⟩
  have hhalf0 : sigma0 + sigma0 = E.sum id := hhalf.1 _ _ hsigma0
  let B := recohEdgeDecode E sigma0
  have hBcard : B.card = 3 := (recoh_edge_decode_card E sigma0).trans hEcard
  have hu : ((a + b + c) - sigma0) + ((a + b + c) - sigma0) = 0 :=
    (double_eq_iff_two_torsion sigma0 (a + b + c)).mp (hhalf0.trans hsum.symm)
  have hdecode : recohEdgeDecode E (a + b + c) = ({a, b, c} : Finset G) := by
    have ha : (a + b + c) - (a + b) = c := by abel
    have hb : (a + b + c) - (a + c) = b := by abel
    have hc : (a + b + c) - (b + c) = a := by abel
    ext x
    simp only [recohEdgeDecode, E, Finset.image_insert, Finset.image_singleton,
      ha, hb, hc, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hBS : OrdinaryPartner B ({a, b, c} : Finset G) := by
    refine ⟨(a + b + c) - sigma0, hu, ?_⟩
    exact hdecode.symm.trans (recoh_edge_decode_change_half E (a + b + c) sigma0)
  have hBsq : orderedSquare B = R :=
    (funext (orderedSquare_eq_of_ordinaryPartner B _ hBcard hBS)).trans hsquare
  have hraw : B ∈ recohParityRawSeeds U R half := by
    unfold recohParityRawSeeds
    rw [hodd, hDcard, if_pos rfl, hedges, if_pos ⟨hEcard, hguard⟩, hsigma0]
    exact Finset.mem_singleton.mpr rfl
  refine ⟨B, Finset.mem_filter.mpr ⟨hraw, hBcard, ?_⟩, hBS⟩
  exact (recoh_sparse_square_check_iff U B R hR).mpr hBsq

/-- The one-odd branch covers every triple whose last two points have the
same double, including the all-equal-doubles profile. -/
theorem recoh_parity_complete_paired
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (hhalf : RecohHalfSolverSpec half) (hR : ∀ z, R z ≠ 0 → z ∈ U)
    (x y z : G) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hyz2 : y + y = z + z)
    (hsquare : orderedSquare ({x, y, z} : Finset G) = R) :
    ∃ B ∈ recohParityRepresentatives U R half,
      OrdinaryPartner B ({x, y, z} : Finset G) := by
  let a := y - x
  let b := z - x
  let N : Finset G := {0, a, b}
  let Q : Finset G := {a + a, a, b, a + b}
  have ha : a ≠ 0 := by
    intro h
    exact hxy (sub_eq_zero.mp h).symm
  have hb : b ≠ 0 := by
    intro h
    exact hxz (sub_eq_zero.mp h).symm
  have hab : a ≠ b := by
    intro h
    have hh := congrArg (fun t : G => t + x) h
    exact hyz (by simpa [a, b] using hh)
  have hab2 : a + a = b + b := by
    calc
      a + a = (y + y) - (x + x) := by dsimp [a]; abel
      _ = (z + z) - (x + x) := by rw [hyz2]
      _ = b + b := by dsimp [b]; abel
  have hNcard : N.card = 3 := by simp [N, Ne.symm ha, Ne.symm hb, hab]
  have hS : ({x, y, z} : Finset G) = translateSupport N x := by
    simp [N, translateSupport_three, a, b]
  obtain ⟨hQcard, hQexp⟩ := parity_quad_expansion a b ha hb hab hab2
  have hexp : ∀ w, R (w + (x + x)) = recohParityIndicator ({0} : Finset G) w +
      2 * recohParityIndicator Q w := by
    intro w
    rw [← hsquare, hS, recoh_ordered_square_translate_shift]
    exact hQexp w
  have hparity : ∀ w, R w % 2 = if x + x = w then 1 else 0 := by
    intro w
    rw [← hsquare, orderedSquare_three x y z w hxy hxz hyz,
      tripleSquareCoeff_mod_two]
    simp only [diagCoeff, hyz2]
    split_ifs <;> omega
  have hodd := parity_odd_eq_singleton U R hR (x + x) hparity
  have hquad := parity_quad_eq_of_expansion U Q R hR (x + x) hexp
  have hguard := parity_single_guard_of_expansion U Q R hR (x + x) hexp
  obtain ⟨c, hc⟩ := hhalf.2 (x + x) ⟨x, rfl⟩
  have hc2 : c + c = x + x := hhalf.1 _ _ hc
  let B := translateSupport N c
  have hBcard : B.card = 3 := (translateSupport_card N c).trans hNcard
  have hu : (x - c) + (x - c) = 0 :=
    (double_eq_iff_two_torsion c x).mp hc2
  have hBS : OrdinaryPartner B ({x, y, z} : Finset G) := by
    refine ⟨x - c, hu, ?_⟩
    rw [hS]
    change translateSupport N x = translateSupport (translateSupport N c) (x - c)
    rw [translateSupport_add]
    congr 1
    abel
  have hBsq : orderedSquare B = R :=
    (funext (orderedSquare_eq_of_ordinaryPartner B _ hBcard hBS)).trans hsquare
  have hP : ({a, b} : Finset G) ∈ recohParityLocalPairs Q := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_, ?_⟩
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl <;> simp [Q]
    · simp [hab]
    · simp [Ne.symm ha, Ne.symm hb]
    · intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · rfl
      · exact hab2
      · exact hab2.symm
      · rfl
  have hsingle : B ∈ recohParitySingleSeeds U R half (x + x) := by
    have hQ4 : (recohParityQuad U R (x + x)).card = 4 := by rw [hquad]; exact hQcard
    unfold recohParitySingleSeeds
    rw [if_pos ⟨hQ4, hguard⟩, hc, hquad]
    exact Finset.mem_image.mpr ⟨{a, b}, hP, rfl⟩
  have hraw : B ∈ recohParityRawSeeds U R half := by
    simpa [recohParityRawSeeds, hodd] using hsingle
  refine ⟨B, Finset.mem_filter.mpr ⟨hraw, hBcard, ?_⟩, hBS⟩
  exact (recoh_sparse_square_check_iff U B R hR).mpr hBsq

/-- Every realizable ordered square is covered by the compact family. -/
theorem recoh_parity_representatives_complete
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (hhalf : RecohHalfSolverSpec half) (hR : ∀ z, R z ≠ 0 → z ∈ U)
    (S : Finset G) (hS : S.card = 3) (hsquare : orderedSquare S = R) :
    ∃ B ∈ recohParityRepresentatives U R half, OrdinaryPartner B S := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS
  by_cases hbc2 : b + b = c + c
  · exact recoh_parity_complete_paired U R half hhalf hR a b c hab hac hbc hbc2 hsquare
  by_cases hab2 : a + a = b + b
  · have hs : ({a, b, c} : Finset G) = {c, a, b} := (support_rotate c a b).symm
    rw [hs] at hsquare ⊢
    exact recoh_parity_complete_paired U R half hhalf hR c a b
      (Ne.symm hac) (Ne.symm hbc) hab hab2 hsquare
  by_cases hac2 : a + a = c + c
  · have hs : ({a, b, c} : Finset G) = {b, a, c} := by
      ext w
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hs] at hsquare ⊢
    exact recoh_parity_complete_paired U R half hhalf hR b a c
      (Ne.symm hab) hbc hac hac2 hsquare
  exact recoh_parity_complete_distinct U R half hhalf hR a b c
    hab hac hbc hab2 hac2 hbc2 hsquare

theorem recoh_parity_representatives_cover
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (hhalf : RecohHalfSolverSpec half) (hR : ∀ z, R z ≠ 0 → z ∈ U) :
    RecohParityCover R (recohParityRepresentatives U R half) := by
  exact ⟨recoh_parity_representatives_sound U R half hR,
    recoh_parity_representatives_complete U R half hhalf hR⟩







end Couret.STROBO2TORS


