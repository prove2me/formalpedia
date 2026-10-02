-- Prove2me | solution 1 for BookSixth.high_girth_chromatic
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T22:08:42.495925+00:00
-- url     : https://prove2.me/submissions/41d3d5ea-3d5b-4c32-b639-ea1d869664cc

import Definitions.Def_BookSixth
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/- Component: Alteration.lean -/
set_option autoImplicit false



namespace HighGirth

/-- A length at most `k` and a cyclically ordered vertex tuple. -/
abbrev CycleCode (N k : ℕ) := Σ l : Fin (k + 1), (Fin l.val → Fin N)

/-- The literal ordered-cycle condition used by `BookSixth.HasCycle`. -/
def IsCycleCode {N k : ℕ} (G : SimpleGraph (Fin N)) (c : CycleCode N k) : Prop :=
  3 ≤ c.1.val ∧ Function.Injective c.2 ∧
    ∀ i j : Fin c.1.val, j.val = (i.val + 1) % c.1.val → G.Adj (c.2 i) (c.2 j)

/-- Ordered short cycles; rotations and reversals are deliberately counted separately. -/
noncomputable def shortCycles {N : ℕ} (G : SimpleGraph (Fin N)) (k : ℕ) :
    Finset (CycleCode N k) := by
  classical
  exact Finset.univ.filter (IsCycleCode G)

theorem mem_shortCycles {N : ℕ} (G : SimpleGraph (Fin N)) (k : ℕ)
    (c : CycleCode N k) : c ∈ shortCycles G k ↔ IsCycleCode G c := by
  classical
  simp only [shortCycles, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A valid cycle has a first vertex, including when the ambient graph is empty. -/
def cycleHead {N k : ℕ} {G : SimpleGraph (Fin N)} (c : CycleCode N k)
    (hc : IsCycleCode G c) : Fin N :=
  c.2 ⟨0, by have h := hc.1; omega⟩

/-- Delete only the first vertex of each ordered short cycle. -/
noncomputable def deletedVertices {N : ℕ} (G : SimpleGraph (Fin N)) (k : ℕ) :
    Finset (Fin N) := by
  classical
  exact (shortCycles G k).attach.image
    (fun c => cycleHead c.val ((mem_shortCycles G k c.val).mp c.property))

theorem deletedVertices_card_le {N : ℕ} (G : SimpleGraph (Fin N)) (k : ℕ) :
    (deletedVertices G k).card ≤ (shortCycles G k).card := by
  classical
  calc
    (deletedVertices G k).card ≤ (shortCycles G k).attach.card := Finset.card_image_le
    _ = (shortCycles G k).card := Finset.card_attach

theorem cycleHead_mem_deleted {N k : ℕ} (G : SimpleGraph (Fin N))
    (c : CycleCode N k) (hc : IsCycleCode G c) :
    cycleHead c hc ∈ deletedVertices G k := by
  classical
  have hmem : c ∈ shortCycles G k := (mem_shortCycles G k c).mpr hc
  apply Finset.mem_image.mpr
  refine ⟨⟨c, hmem⟩, Finset.mem_attach _ _, ?_⟩
  rfl

/-- A large induced vertex set cannot be colored with `k` colors if the original
 graph has no independent set of size `t`. -/
theorem not_colorable_comap {N M k t : ℕ} (G : SimpleGraph (Fin N))
    (f : Fin M → Fin N) (hf : Function.Injective f)
    (hind : ∀ S : Finset (Fin N), S.card = t →
      ∃ u ∈ S, ∃ v ∈ S, G.Adj u v)
    (hsize : k * (t - 1) < M) :
    ¬ BookSixth.HasColoring (G.comap f) k := by
  classical
  rintro ⟨c, hc⟩
  have hcount : Fintype.card (Fin k) * (t - 1) < Fintype.card (Fin M) := by
    simpa only [Fintype.card_fin] using hsize
  obtain ⟨color, hcolor⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card (f := c) hcount
  have ht : t ≤ (Finset.univ.filter (fun v : Fin M => c v = color)).card := by
    omega
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq ht
  have himage : (S.image f).card = t := by
    rw [Finset.card_image_of_injective S hf, hScard]
  obtain ⟨u, hu, v, hv, huv⟩ := hind (S.image f) himage
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
  have hca : c a = color := (Finset.mem_filter.mp (hS ha)).2
  have hcb : c b = color := (Finset.mem_filter.mp (hS hb)).2
  exact hc a b huv (hca.trans hcb.symm)

/-- Finite alteration: deleting one vertex from each short cycle leaves a graph
 whose chromatic number and girth exceed `k`, provided the explicit counting
 budget and independent-set obstruction hold in the original graph. -/
theorem alteration {N k t : ℕ} (G : SimpleGraph (Fin N))
    (hind : ∀ S : Finset (Fin N), S.card = t →
      ∃ u ∈ S, ∃ v ∈ S, G.Adj u v)
    (hbudget : k * (t - 1) + (shortCycles G k).card < N) :
    ∃ M : ℕ, ∃ H : SimpleGraph (Fin M), ¬ BookSixth.HasColoring H k ∧
      ∀ l : ℕ, l ≤ k → ¬ BookSixth.HasCycle H l := by
  classical
  let W := {v : Fin N // v ∉ deletedVertices G k}
  let e : Fin (Fintype.card W) ≃ W := (Fintype.equivFin W).symm
  let f : Fin (Fintype.card W) → Fin N := fun v => (e v).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hWcard : Fintype.card W = N - (deletedVertices G k).card := by
    change Fintype.card {v : Fin N // ¬ v ∈ deletedVertices G k} = _
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_fin, Fintype.card_coe]
  have hsurvive : k * (t - 1) < Fintype.card W := by
    have hdeleted := deletedVertices_card_le G k
    rw [hWcard]
    omega
  refine ⟨Fintype.card W, G.comap f, not_colorable_comap G f hf hind hsurvive, ?_⟩
  intro l hl hcycle
  obtain ⟨hl3, v, hv, hadj⟩ := hcycle
  let code : CycleCode N k := ⟨⟨l, by omega⟩, fun i => f (v i)⟩
  have hcode : IsCycleCode G code := by
    refine ⟨hl3, hf.comp hv, ?_⟩
    intro i j hij
    exact hadj i j hij
  have hhead := cycleHead_mem_deleted G code hcode
  have hnot : f (v ⟨0, by omega⟩) ∉ deletedVertices G k := (e (v ⟨0, by omega⟩)).property
  exact hnot hhead

end HighGirth



/- Component: CoordinateCounts.lean -/
set_option autoImplicit false
open scoped BigOperators

namespace HighGirth

/-!
Finite coordinate-assignment counts for the random-graph construction.
No graph-existence claim is assumed. The coordinate type can be any finite
representation of unordered distinct vertex pairs. A fixed finite set of
coordinates must be supplied by the caller, so repeated cycle edges cannot
silently be counted as independent coordinates.

Target environment: Lean 4.30.0 / Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f.
This source is an uncompiled local component draft.
-/

/-- Uniform finite probability, expressed as a ratio of exact cardinalities. -/
noncomputable def uniformProbability {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : ℝ :=
  (Nat.card {ω : Ω // P ω} : ℝ) / (Nat.card Ω : ℝ)

section Coordinates

variable {E α : Type*} [Fintype E] [DecidableEq E] [Fintype α] [DecidableEq α]

/-- Independent choices from a possibly different allowed set at every coordinate. -/
theorem card_coordinate_family (allowed : E → Finset α) :
    Fintype.card {ω : E → α // ∀ e, ω e ∈ allowed e} =
      ∏ e : E, (allowed e).card := by
  classical
  calc
    _ = Fintype.card (∀ e : E, {a : α // a ∈ allowed e}) :=
      Fintype.card_congr (Equiv.subtypePiEquivPi
        (β := fun _ : E => α) (p := fun e a => a ∈ allowed e))
    _ = _ := by simp only [Fintype.card_pi, Fintype.card_coe]

/-- Restrict `J` to one common allowed set; all other coordinates remain free. -/
theorem card_coordinate_restrictions (J : Finset E) (T : Finset α) :
    Fintype.card {ω : E → α // ∀ e ∈ J, ω e ∈ T} =
      T.card ^ J.card * Fintype.card α ^ (Fintype.card E - J.card) := by
  classical
  let allowed : E → Finset α := fun e => if e ∈ J then T else Finset.univ
  have heq : Fintype.card {ω : E → α // ∀ e ∈ J, ω e ∈ T} =
      Fintype.card {ω : E → α // ∀ e, ω e ∈ allowed e} := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro ω
    constructor
    · intro h e
      by_cases he : e ∈ J
      · simpa only [allowed, if_pos he] using h e he
      · simp only [allowed, if_neg he, Finset.mem_univ]
    · intro h e he
      simpa only [allowed, if_pos he] using h e
  rw [heq, card_coordinate_family]
  have hprod : (∏ e : E, (allowed e).card) =
      ∏ e : E, if e ∈ J then T.card else Fintype.card α := by
    apply Finset.prod_congr rfl
    intro e he
    by_cases hJ : e ∈ J <;> simp [allowed, hJ]
  rw [hprod, Finset.prod_ite]
  have hin : Finset.univ.filter (fun e : E => e ∈ J) = J := by
    ext e
    simp
  have hout : Finset.univ.filter (fun e : E => ¬e ∈ J) = Jᶜ := by
    ext e
    simp
  rw [hin, hout]
  simp only [Finset.prod_const, Finset.card_compl]

theorem card_coordinates_eq (J : Finset E) (a : α) :
    Fintype.card {ω : E → α // ∀ e ∈ J, ω e = a} =
      Fintype.card α ^ (Fintype.card E - J.card) := by
  simpa using card_coordinate_restrictions J ({a} : Finset α)

theorem card_coordinates_ne (J : Finset E) (a : α) :
    Fintype.card {ω : E → α // ∀ e ∈ J, ω e ≠ a} =
      (Fintype.card α - 1) ^ J.card * Fintype.card α ^ (Fintype.card E - J.card) := by
  have h := card_coordinate_restrictions J (Finset.univ.erase a)
  rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ] at h
  simpa using h

/-- Exact finite probability of a fixed-coordinate allowed-set event. -/
theorem uniformProbability_coordinate_restrictions
    (J : Finset E) (T : Finset α) (hα : 0 < Fintype.card α) :
    uniformProbability (fun ω : E → α => ∀ e ∈ J, ω e ∈ T) =
      ((T.card : ℝ) / (Fintype.card α : ℝ)) ^ J.card := by
  classical
  unfold uniformProbability
  simp only [Nat.card_eq_fintype_card]
  rw [card_coordinate_restrictions J T, Fintype.card_fun]
  push_cast
  have hq : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast hα.ne'
  have hpow : (Fintype.card α : ℝ) ^ Fintype.card E =
      (Fintype.card α : ℝ) ^ (Fintype.card E - J.card) *
        (Fintype.card α : ℝ) ^ J.card := by
    rw [← pow_add, Nat.sub_add_cancel (Finset.card_le_univ J)]
  rw [hpow, div_pow]
  field_simp [hq] <;> ring

theorem uniformProbability_coordinates_eq
    (J : Finset E) (a : α) (hα : 0 < Fintype.card α) :
    uniformProbability (fun ω : E → α => ∀ e ∈ J, ω e = a) =
      (1 / (Fintype.card α : ℝ)) ^ J.card := by
  simpa using uniformProbability_coordinate_restrictions J ({a} : Finset α) hα

theorem uniformProbability_coordinates_ne
    (J : Finset E) (a : α) (hα : 0 < Fintype.card α) :
    uniformProbability (fun ω : E → α => ∀ e ∈ J, ω e ≠ a) =
      (1 - 1 / (Fintype.card α : ℝ)) ^ J.card := by
  have h := uniformProbability_coordinate_restrictions J (Finset.univ.erase a) hα
  rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ] at h
  have hq : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast hα.ne'
  have hcard : ((Fintype.card α - 1 : ℕ) : ℝ) = (Fintype.card α : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr hα), Nat.cast_one]
  rw [hcard, sub_div, div_self hq] at h
  simpa using h

end Coordinates

section FinColors

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The exact present-edge count in the `Fin q` sample space. -/
theorem card_all_zero (q : ℕ) (hq : 0 < q) (J : Finset E) :
    Fintype.card {ω : E → Fin q // ∀ e ∈ J, ω e = ⟨0, hq⟩} =
      q ^ (Fintype.card E - J.card) := by
  simpa only [Fintype.card_fin] using card_coordinates_eq J (⟨0, hq⟩ : Fin q)

/-- The exact absent-edge count in the `Fin q` sample space. -/
theorem card_all_nonzero (q : ℕ) (hq : 0 < q) (J : Finset E) :
    Fintype.card {ω : E → Fin q // ∀ e ∈ J, ω e ≠ ⟨0, hq⟩} =
      (q - 1) ^ J.card * q ^ (Fintype.card E - J.card) := by
  simpa only [Fintype.card_fin] using card_coordinates_ne J (⟨0, hq⟩ : Fin q)

theorem uniformProbability_all_zero (q : ℕ) (hq : 0 < q) (J : Finset E) :
    uniformProbability (fun ω : E → Fin q => ∀ e ∈ J, ω e = ⟨0, hq⟩) =
      (1 / (q : ℝ)) ^ J.card := by
  simpa only [Fintype.card_fin] using
    uniformProbability_coordinates_eq J (⟨0, hq⟩ : Fin q) (by simpa using hq)

theorem uniformProbability_all_nonzero (q : ℕ) (hq : 0 < q) (J : Finset E) :
    uniformProbability (fun ω : E → Fin q => ∀ e ∈ J, ω e ≠ ⟨0, hq⟩) =
      (1 - 1 / (q : ℝ)) ^ J.card := by
  simpa only [Fintype.card_fin] using
    uniformProbability_coordinates_ne J (⟨0, hq⟩ : Fin q) (by simpa using hq)

end FinColors

end HighGirth



/- Component: ProbabilityBounds.lean -/
set_option autoImplicit false
open scoped BigOperators

namespace HighGirth

/-!
Finite union, expectation and Markov bounds, followed by actual good-outcome
selection. Standalone draft for Lean 4.30.0 / Mathlib c5ea003. This includes
only CoordinateCounts.lean's exact uniformProbability definition, which must
be deduplicated when the two components are combined. No graph existence,
edge independence or desired good-outcome statement is assumed.
-/


/-- Uniform arithmetic mean on the actual finite sample space. -/
noncomputable def uniformMean {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) : ℝ :=
  (∑ ω : Ω, X ω) / (Fintype.card Ω : ℝ)

/-- Number of events from a finite family that occur at one outcome. -/
noncomputable def countEvents {ι Ω : Type*} (I : Finset ι)
    (P : ι → Ω → Prop) (ω : Ω) : ℕ := by
  classical
  exact (I.filter (fun i => P i ω)).card

section FiniteProbability

variable {Ω : Type*} [Fintype Ω]

theorem uniformProbability_congr {P Q : Ω → Prop} (h : ∀ ω, P ω ↔ Q ω) :
    uniformProbability P = uniformProbability Q := by
  classical
  have hc : Nat.card {ω : Ω // P ω} = Nat.card {ω : Ω // Q ω} :=
    Nat.card_congr (Equiv.subtypeEquivRight h)
  unfold uniformProbability
  rw [hc]

theorem uniformProbability_eq_mean_indicator (P : Ω → Prop) [DecidablePred P] :
    uniformProbability P = uniformMean (fun ω => if P ω then (1 : ℝ) else 0) := by
  classical
  unfold uniformProbability uniformMean
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype, Finset.card_filter]
  push_cast
  simp

theorem uniformMean_mono {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) :
    uniformMean X ≤ uniformMean Y := by
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun ω _ => h ω)) (Nat.cast_nonneg _)

theorem uniformMean_add (X Y : Ω → ℝ) :
    uniformMean (fun ω => X ω + Y ω) = uniformMean X + uniformMean Y := by
  unfold uniformMean
  rw [Finset.sum_add_distrib, add_div]

theorem uniformMean_mul_left (a : ℝ) (X : Ω → ℝ) :
    uniformMean (fun ω => a * X ω) = a * uniformMean X := by
  unfold uniformMean
  rw [← Finset.mul_sum]
  ring

theorem uniformMean_sum {ι : Type*} (I : Finset ι) (X : ι → Ω → ℝ) :
    uniformMean (fun ω => ∑ i ∈ I, X i ω) = ∑ i ∈ I, uniformMean (X i) := by
  unfold uniformMean
  rw [Finset.sum_comm, Finset.sum_div]

/-- Expected number of occurring events equals the sum of their probabilities. -/
theorem uniformMean_count {ι : Type*} (I : Finset ι) (P : ι → Ω → Prop) :
    uniformMean (fun ω => (countEvents I P ω : ℝ)) =
      ∑ i ∈ I, uniformProbability (P i) := by
  classical
  have hcount (ω : Ω) : (countEvents I P ω : ℝ) =
      ∑ i ∈ I, if P i ω then (1 : ℝ) else 0 := by
    unfold countEvents
    rw [Finset.card_filter]
    push_cast
    simp
  calc
    _ = uniformMean (fun ω => ∑ i ∈ I, if P i ω then (1 : ℝ) else 0) :=
      congrArg uniformMean (funext hcount)
    _ = ∑ i ∈ I, uniformMean (fun ω => if P i ω then (1 : ℝ) else 0) :=
      uniformMean_sum I _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (uniformProbability_eq_mean_indicator (P i)).symm

/-- Finite union bound, without any independence hypothesis. -/
theorem uniformProbability_exists_le {ι : Type*} (I : Finset ι) (P : ι → Ω → Prop) :
    uniformProbability (fun ω => ∃ i ∈ I, P i ω) ≤
      ∑ i ∈ I, uniformProbability (P i) := by
  classical
  have hpoint (ω : Ω) :
      (if ∃ i ∈ I, P i ω then (1 : ℝ) else 0) ≤
        ∑ i ∈ I, if P i ω then (1 : ℝ) else 0 := by
    by_cases h : ∃ i ∈ I, P i ω
    · rw [if_pos h]
      obtain ⟨i, hi, hPi⟩ := h
      have hs := Finset.single_le_sum
        (f := fun j => if P j ω then (1 : ℝ) else 0)
        (s := I) (fun j hj => by dsimp only; split_ifs <;> norm_num) hi
      simpa only [if_pos hPi] using hs
    · rw [if_neg h]
      exact Finset.sum_nonneg (fun i hi => by split_ifs <;> norm_num)
  rw [uniformProbability_eq_mean_indicator]
  calc
    _ ≤ uniformMean (fun ω => ∑ i ∈ I, if P i ω then (1 : ℝ) else 0) :=
      uniformMean_mono hpoint
    _ = ∑ i ∈ I, uniformMean (fun ω => if P i ω then (1 : ℝ) else 0) :=
      uniformMean_sum I _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (uniformProbability_eq_mean_indicator (P i)).symm

theorem uniformProbability_or_le (P Q : Ω → Prop) :
    uniformProbability (fun ω => P ω ∨ Q ω) ≤
      uniformProbability P + uniformProbability Q := by
  classical
  have hpoint (ω : Ω) : (if P ω ∨ Q ω then (1 : ℝ) else 0) ≤
      (if P ω then (1 : ℝ) else 0) + (if Q ω then (1 : ℝ) else 0) := by
    by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq]
  rw [uniformProbability_eq_mean_indicator]
  calc
    _ ≤ uniformMean (fun ω =>
        (if P ω then (1 : ℝ) else 0) + (if Q ω then (1 : ℝ) else 0)) :=
      uniformMean_mono hpoint
    _ = _ := by
      rw [uniformMean_add, ← uniformProbability_eq_mean_indicator,
        ← uniformProbability_eq_mean_indicator]

/-- Markov's inequality obtained directly by summing the indicator bound. -/
theorem uniformProbability_nat_ge_le (C : Ω → ℕ) (a : ℝ) (ha : 0 < a) :
    uniformProbability (fun ω => a ≤ (C ω : ℝ)) ≤
      uniformMean (fun ω => (C ω : ℝ)) / a := by
  classical
  have hpoint (ω : Ω) : a * (if a ≤ (C ω : ℝ) then (1 : ℝ) else 0) ≤ C ω := by
    by_cases h : a ≤ (C ω : ℝ)
    · simpa only [if_pos h, mul_one] using h
    · simp only [if_neg h, mul_zero, Nat.cast_nonneg]
  have hmean := uniformMean_mono hpoint
  rw [uniformMean_mul_left, ← uniformProbability_eq_mean_indicator] at hmean
  exact (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hmean)

theorem uniformProbability_eq_one_of_forall [Nonempty Ω]
    (P : Ω → Prop) (hP : ∀ ω, P ω) : uniformProbability P = 1 := by
  classical
  have hfilter : Finset.univ.filter P = (Finset.univ : Finset Ω) := by
    ext ω
    simp [hP ω]
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold uniformProbability
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype, hfilter, Finset.card_univ, div_self hcard]

/-- A sample simultaneously avoids the bad event and has fewer than `N/2` counted objects. -/
theorem exists_good_outcome [Nonempty Ω] (C : Ω → ℕ) (B : Ω → Prop)
    (N : ℝ) (hN : 0 < N)
    (hmean : uniformMean (fun ω => (C ω : ℝ)) ≤ N / 4)
    (hbad : uniformProbability B < 1 / 4) :
    ∃ ω : Ω, ¬B ω ∧ (C ω : ℝ) < N / 2 := by
  classical
  let P : Ω → Prop := fun ω => N / 2 ≤ (C ω : ℝ)
  have hhalf : 0 < N / 2 := by positivity
  have hmark : uniformProbability P ≤ (1 / 2 : ℝ) := by
    refine (uniformProbability_nat_ge_le C (N / 2) hhalf).trans ?_
    apply (div_le_iff₀ hhalf).mpr
    nlinarith [hmean]
  have hunion := uniformProbability_or_le B P
  by_contra hnone
  push Not at hnone
  have hall (ω : Ω) : B ω ∨ P ω := by
    by_cases hB : B ω
    · exact Or.inl hB
    · exact Or.inr (hnone ω hB)
  have hone := uniformProbability_eq_one_of_forall (fun ω => B ω ∨ P ω) hall
  rw [hone] at hunion
  linarith

end FiniteProbability

end HighGirth



/- Component: GraphEvents.lean -/
set_option autoImplicit false

namespace HighGirth

/-- Independent finite colors on all unordered pairs. Diagonal coordinates are unused. -/
def sampleGraph {N q : ℕ} (hq : 0 < q) (ω : Sym2 (Fin N) → Fin q) :
    SimpleGraph (Fin N) where
  Adj u v := u ≠ v ∧ ω s(u, v) = ⟨0, hq⟩
  symm := by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rw [Sym2.eq_swap]
    exact h.2
  loopless := ⟨fun u h => h.1 rfl⟩

@[simp] theorem sampleGraph_adj {N q : ℕ} (hq : 0 < q)
    (ω : Sym2 (Fin N) → Fin q) (u v : Fin N) :
    (sampleGraph hq ω).Adj u v ↔ u ≠ v ∧ ω s(u, v) = ⟨0, hq⟩ := Iff.rfl

/-- The successor coordinate in a cyclic tuple, in the public natural-modulo form. -/
theorem rotate_val {l : ℕ} (hl : 3 ≤ l) (i : Fin l) :
    (finRotate l i).val = (i.val + 1) % l := by
  letI : NeZero l := ⟨by omega⟩
  rw [finRotate_apply, Fin.val_add, Fin.val_one']
  rw [Nat.mod_eq_of_lt (by omega : 1 < l)]

private theorem rotate_val_cases {l : ℕ} (hl : 3 ≤ l) (i : Fin l) :
    (finRotate l i).val = if i.val + 1 < l then i.val + 1 else 0 := by
  rw [rotate_val hl]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have hi : i.val + 1 = l := by omega
    rw [hi, Nat.mod_self]

/-- A cycle of length at least three has no stationary successor. -/
theorem rotate_ne_self {l : ℕ} (hl : 3 ≤ l) (i : Fin l) :
    finRotate l i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  rw [rotate_val_cases hl] at hv
  split_ifs at hv <;> omega

/-- Two successor steps cannot reverse an edge in a cycle of length at least three. -/
theorem rotate_not_two_cycle {l : ℕ} (hl : 3 ≤ l) (i j : Fin l)
    (hij : finRotate l i = j) (hji : finRotate l j = i) : False := by
  have hi := congrArg Fin.val hij
  have hj := congrArg Fin.val hji
  rw [rotate_val_cases hl] at hi hj
  split_ifs at hi hj <;> omega

/-- The distinct edge coordinates constrained by one cyclic tuple. -/
def cycleEdges {N l : ℕ} (v : Fin l → Fin N) : Finset (Sym2 (Fin N)) :=
  Finset.univ.image (fun i => s(v i, v (finRotate l i)))

/-- Injective vertex tuples of length at least three give distinct unordered cycle edges. -/
theorem cycle_edge_injective {N l : ℕ} (hl : 3 ≤ l) (v : Fin l → Fin N)
    (hv : Function.Injective v) :
    Function.Injective (fun i : Fin l => s(v i, v (finRotate l i))) := by
  intro i j h
  rcases Sym2.eq_iff.mp h with h | h
  · exact hv h.1
  · exact False.elim (rotate_not_two_cycle hl i j (hv h.2) (hv h.1).symm)

theorem cycleEdges_card {N l : ℕ} (hl : 3 ≤ l) (v : Fin l → Fin N)
    (hv : Function.Injective v) : (cycleEdges v).card = l := by
  rw [cycleEdges, Finset.card_image_of_injective _ (cycle_edge_injective hl v hv)]
  simp only [Finset.card_univ, Fintype.card_fin]

/-- Exact edge-event description of the cyclic adjacency clause in the public definition. -/
theorem cycle_event_iff {N q l : ℕ} (hq : 0 < q)
    (ω : Sym2 (Fin N) → Fin q) (hl : 3 ≤ l) (v : Fin l → Fin N)
    (hv : Function.Injective v) :
    (∀ i j : Fin l, j.val = (i.val + 1) % l →
      (sampleGraph hq ω).Adj (v i) (v j)) ↔
      ∀ e ∈ cycleEdges v, ω e = ⟨0, hq⟩ := by
  constructor
  · intro h e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    exact (h i (finRotate l i) (rotate_val hl i)).2
  · intro h i j hij
    have hj : j = finRotate l i := Fin.ext (hij.trans (rotate_val hl i).symm)
    subst j
    refine ⟨?_, ?_⟩
    · intro heq
      exact rotate_ne_self hl i (hv heq).symm
    · exact h _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- All unordered pairs of distinct vertices inside a set. -/
def independentEdges {N : ℕ} (S : Finset (Fin N)) : Finset (Sym2 (Fin N)) :=
  S.offDiag.image Sym2.mk.uncurry

theorem independentEdges_card {N : ℕ} (S : Finset (Fin N)) :
    (independentEdges S).card = S.card.choose 2 :=
  Sym2.card_image_offDiag S

/-- A vertex set is independent precisely when all its internal edge colors are nonzero. -/
theorem independent_event_iff {N q : ℕ} (hq : 0 < q)
    (ω : Sym2 (Fin N) → Fin q) (S : Finset (Fin N)) :
    (∀ u ∈ S, ∀ v ∈ S, ¬ (sampleGraph hq ω).Adj u v) ↔
      ∀ e ∈ independentEdges S, ω e ≠ ⟨0, hq⟩ := by
  constructor
  · intro hind e he hzero
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hu, hv, hne⟩ := Finset.mem_offDiag.mp huv
    exact hind u hu v hv ⟨hne, hzero⟩
  · intro h u hu v hv hadj
    have he : s(u, v) ∈ independentEdges S :=
      Finset.mem_image.mpr ⟨(u, v), Finset.mem_offDiag.mpr ⟨hu, hv, hadj.1⟩, rfl⟩
    exact h _ he hadj.2

/-- The edge-containing formulation needed by deterministic alteration. -/
theorem not_independent_iff_edge {N : ℕ} (G : SimpleGraph (Fin N))
    (S : Finset (Fin N)) :
    ¬ (∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v) ↔
      ∃ u ∈ S, ∃ v ∈ S, G.Adj u v := by
  classical
  simp only [not_forall, not_not, exists_prop]

end HighGirth



/- Component: NumericBounds.lean -/
noncomputable section
open scoped BigOperators
namespace HighGirth

def densityBase (k : ℕ) : ℕ := 128 * k ^ 2
def colorCount (k : ℕ) : ℕ := densityBase k ^ k
def independentSize (k : ℕ) : ℕ := 64 * k * colorCount k
def vertexCount (k : ℕ) : ℕ := densityBase k * colorCount k

theorem parameters (k : ℕ) (hk : 2 ≤ k) :
    1 ≤ colorCount k ∧ 2 ≤ independentSize k ∧ 1 ≤ vertexCount k ∧
    vertexCount k = 2 * k * independentSize k ∧
    4 * k * colorCount k ≤ vertexCount k := by
  have hk1 : 1 ≤ k := by omega
  have ha : 1 ≤ densityBase k := by unfold densityBase; nlinarith
  have hq : 1 ≤ colorCount k := one_le_pow₀ ha
  have ht : 2 ≤ independentSize k := by
    unfold independentSize
    nlinarith
  refine ⟨hq, ht, ?_, ?_, ?_⟩
  · unfold vertexCount
    nlinarith
  · unfold vertexCount independentSize densityBase
    ring
  · have hka : 4 * k ≤ densityBase k := by unfold densityBase; nlinarith
    exact Nat.mul_le_mul_right _ hka

theorem short_cycle_expectation_bound (k : ℕ) (hk : 2 ≤ k) :
    (∑ l ∈ Finset.Icc 3 k,
      ((vertexCount k : ℝ) / colorCount k) ^ l) ≤ (vertexCount k : ℝ) / 4 := by
  have hq := (parameters k hk).1
  have ha : 1 ≤ densityBase k := by unfold densityBase; nlinarith
  have hq0 : (colorCount k : ℝ) ≠ 0 := by exact_mod_cast (by omega : colorCount k ≠ 0)
  have hratio : (vertexCount k : ℝ) / colorCount k = densityBase k := by
    unfold vertexCount
    push_cast
    exact mul_div_cancel_right₀ _ hq0
  rw [hratio]
  have hterm (l : ℕ) (hl : l ∈ Finset.Icc 3 k) :
      (densityBase k : ℝ) ^ l ≤ colorCount k := by
    have hal : (1 : ℝ) ≤ densityBase k := by exact_mod_cast ha
    have := pow_le_pow_right₀ hal (Finset.mem_Icc.mp hl).2
    simpa [colorCount] using this
  calc
    _ ≤ ∑ _l ∈ Finset.Icc 3 k, (colorCount k : ℝ) := Finset.sum_le_sum hterm
    _ = ((Finset.Icc 3 k).card : ℝ) * colorCount k := by simp
    _ ≤ (k : ℝ) * colorCount k := by
      gcongr
      exact_mod_cast (show (Finset.Icc 3 k).card ≤ k by simp)
    _ ≤ (vertexCount k : ℝ) / 4 := by
      have hb := (parameters k hk).2.2.2.2
      have hb' : (4 : ℝ) * k * colorCount k ≤ vertexCount k := by exact_mod_cast hb
      linarith

theorem independent_exponent_bound (k : ℕ) (hk : 2 ≤ k) :
    8 * (vertexCount k : ℝ) ≤
      ((independentSize k).choose 2 : ℝ) / colorCount k := by
  have hq := (parameters k hk).1
  have ht := (parameters k hk).2.1
  have hq0 : (0 : ℝ) < colorCount k := by exact_mod_cast (by omega : 0 < colorCount k)
  have ht2 : (2 : ℝ) ≤ independentSize k := by exact_mod_cast ht
  rw [Nat.cast_choose_two]
  apply (le_div_iff₀ hq0).mpr
  have hmain : 8 * (vertexCount k : ℝ) * colorCount k = (independentSize k : ℝ)^2 / 4 := by
    unfold vertexCount independentSize densityBase
    push_cast
    ring
  rw [hmain]
  nlinarith

theorem independent_union_bound (k : ℕ) (hk : 2 ≤ k) :
    (2 : ℝ) ^ vertexCount k *
      (1 - 1 / (colorCount k : ℝ)) ^ (independentSize k).choose 2 < 1 / 4 := by
  have hq := (parameters k hk).1
  have hN := (parameters k hk).2.2.1
  have hqR : (1 : ℝ) ≤ colorCount k := by exact_mod_cast hq
  have hbase : 0 ≤ 1 - 1 / (colorCount k : ℝ) := by
    have : 1 / (colorCount k : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hqR
    linarith
  have hpow : (1 - 1 / (colorCount k : ℝ)) ^ (independentSize k).choose 2 ≤
      Real.exp (-((independentSize k).choose 2 : ℝ) / colorCount k) := by
    calc
      _ ≤ Real.exp (-(1 / (colorCount k : ℝ))) ^ (independentSize k).choose 2 :=
        pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg _) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have h2pow : (2 : ℝ) ^ vertexCount k ≤ Real.exp (vertexCount k : ℝ) := by
    simpa only [← Real.exp_nat_mul, mul_one] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h2 (vertexCount k)
  have hNR : (1 : ℝ) ≤ vertexCount k := by exact_mod_cast hN
  calc
    _ ≤ Real.exp (vertexCount k : ℝ) *
        Real.exp (-((independentSize k).choose 2 : ℝ) / colorCount k) :=
      mul_le_mul h2pow hpow (pow_nonneg hbase _) (Real.exp_nonneg _)
    _ = Real.exp ((vertexCount k : ℝ) - ((independentSize k).choose 2 : ℝ) / colorCount k) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-7 * (vertexCount k : ℝ)) := by
      apply Real.exp_le_exp.mpr
      linarith [independent_exponent_bound k hk]
    _ ≤ Real.exp (-7) := Real.exp_le_exp.mpr (by linarith)
    _ < 1 / 4 := by
      rw [Real.exp_neg]
      have he : (8 : ℝ) ≤ Real.exp 7 := by linarith [Real.add_one_le_exp 7]
      have hepos := Real.exp_pos (7 : ℝ)
      apply (inv_lt_iff_one_lt_mul₀ hepos).mpr
      linarith

end HighGirth


/- Component: RandomGraphBounds.fragment.lean -/
namespace HighGirth

/-- A valid ordered cycle has exactly its length many independent edge constraints.
Invalid vertex tuples contribute probability zero. -/
theorem probability_cycle_code_le {N q k : ℕ} (hq : 0 < q)
    (c : CycleCode N k) :
    uniformProbability (fun ω : Sym2 (Fin N) → Fin q =>
      IsCycleCode (sampleGraph hq ω) c) ≤
      if 3 ≤ c.1.val then (1 / (q : ℝ)) ^ c.1.val else 0 := by
  classical
  by_cases hl : 3 ≤ c.1.val
  · rw [if_pos hl]
    by_cases hv : Function.Injective c.2
    · have hevent := uniformProbability_congr
        (P := fun ω : Sym2 (Fin N) → Fin q => IsCycleCode (sampleGraph hq ω) c)
        (Q := fun ω => ∀ e ∈ cycleEdges c.2, ω e = ⟨0, hq⟩)
        (fun ω => by
          simpa only [IsCycleCode, hl, hv, true_and] using
            cycle_event_iff hq ω hl c.2 hv)
      rw [hevent, uniformProbability_all_zero, cycleEdges_card hl c.2 hv]
    · have hevent := uniformProbability_congr
        (P := fun ω : Sym2 (Fin N) → Fin q => IsCycleCode (sampleGraph hq ω) c)
        (Q := fun _ => False) (fun _ => by simp only [IsCycleCode, hv, false_and, and_false])
      rw [hevent]
      have hz : uniformProbability (fun _ : Sym2 (Fin N) → Fin q => False) = 0 := by
        simp [uniformProbability, Nat.card_eq_fintype_card]
      rw [hz]
      positivity
  · rw [if_neg hl]
    have hevent := uniformProbability_congr
      (P := fun ω : Sym2 (Fin N) → Fin q => IsCycleCode (sampleGraph hq ω) c)
      (Q := fun _ => False) (fun _ => by simp only [IsCycleCode, hl, false_and])
    rw [hevent]
    simp [uniformProbability, Nat.card_eq_fintype_card]

/-- Count all vertex tuples as an upper bound, without dividing by rotations or reversals. -/
theorem sum_cycle_code_bounds (N q k : ℕ) :
    (∑ c : CycleCode N k,
      if 3 ≤ c.1.val then (1 / (q : ℝ)) ^ c.1.val else 0) =
      ∑ l ∈ Finset.Icc 3 k, ((N : ℝ) / (q : ℝ)) ^ l := by
  classical
  change (∑ c : Σ l : Fin (k + 1), (Fin l.val → Fin N),
    if 3 ≤ c.1.val then (1 / (q : ℝ)) ^ c.1.val else 0) = _
  rw [Fintype.sum_sigma]
  have hinner (l : Fin (k + 1)) :
      (∑ _v : Fin l.val → Fin N, if 3 ≤ l.val then (1 / (q : ℝ)) ^ l.val else 0) =
        if 3 ≤ l.val then ((N : ℝ) / (q : ℝ)) ^ l.val else 0 := by
    by_cases hl : 3 ≤ l.val
    · simp only [if_pos hl, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      rw [← mul_pow, mul_one_div]
    · simp only [if_neg hl, Finset.sum_const_zero]
  simp_rw [hinner]
  rw [Fin.sum_univ_eq_sum_range
    (fun l : ℕ => if 3 ≤ l then ((N : ℝ) / (q : ℝ)) ^ l else 0) (k + 1)]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range (k + 1)).filter (fun l => 3 ≤ l) = Finset.Icc 3 k := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [hfilter]

/-- Expected number of actual ordered short cycles in the sampled graph. -/
theorem mean_shortCycles_le {N q : ℕ} (hq : 0 < q) (k : ℕ) :
    uniformMean (fun ω : Sym2 (Fin N) → Fin q =>
      ((shortCycles (sampleGraph hq ω) k).card : ℝ)) ≤
      ∑ l ∈ Finset.Icc 3 k, ((N : ℝ) / (q : ℝ)) ^ l := by
  classical
  have hmean : uniformMean (fun ω : Sym2 (Fin N) → Fin q =>
      ((shortCycles (sampleGraph hq ω) k).card : ℝ)) =
      ∑ c : CycleCode N k, uniformProbability
        (fun ω : Sym2 (Fin N) → Fin q => IsCycleCode (sampleGraph hq ω) c) := by
    simpa only [shortCycles, countEvents] using
      uniformMean_count (Finset.univ : Finset (CycleCode N k))
        (fun c (ω : Sym2 (Fin N) → Fin q) => IsCycleCode (sampleGraph hq ω) c)
  rw [hmean, ← sum_cycle_code_bounds N q k]
  exact Finset.sum_le_sum (fun c _ => probability_cycle_code_le hq c)

/-- A fixed independent set constrains each internal unordered pair to a nonzero color. -/
theorem probability_fixed_independent_set {N q : ℕ} (hq : 0 < q)
    (S : Finset (Fin N)) :
    uniformProbability (fun ω : Sym2 (Fin N) → Fin q =>
      ∀ u ∈ S, ∀ v ∈ S, ¬ (sampleGraph hq ω).Adj u v) =
      (1 - 1 / (q : ℝ)) ^ (S.card.choose 2) := by
  classical
  rw [uniformProbability_congr (fun ω => independent_event_iff hq ω S),
    uniformProbability_all_nonzero, independentEdges_card]

/-- A finite union bound over all sets of size `t`; the family is bounded by all `2^N` sets.
This also covers `t > N`, when the family of candidate sets is empty. -/
theorem probability_independent_set_le {N q : ℕ} (hq : 0 < q) (t : ℕ) :
    uniformProbability (fun ω : Sym2 (Fin N) → Fin q =>
      ∃ S : Finset (Fin N), S.card = t ∧
        ∀ u ∈ S, ∀ v ∈ S, ¬ (sampleGraph hq ω).Adj u v) ≤
      (2 : ℝ) ^ N * (1 - 1 / (q : ℝ)) ^ (t.choose 2) := by
  classical
  let I := (Finset.univ : Finset (Fin N)).powersetCard t
  let P := fun (S : Finset (Fin N)) (ω : Sym2 (Fin N) → Fin q) =>
    ∀ u ∈ S, ∀ v ∈ S, ¬ (sampleGraph hq ω).Adj u v
  have hevent : uniformProbability (fun ω : Sym2 (Fin N) → Fin q =>
      ∃ S : Finset (Fin N), S.card = t ∧ P S ω) =
      uniformProbability (fun ω => ∃ S ∈ I, P S ω) := by
    apply uniformProbability_congr
    intro ω
    simp only [I, Finset.mem_powersetCard_univ, exists_prop]
  change uniformProbability (fun ω : Sym2 (Fin N) → Fin q =>
    ∃ S : Finset (Fin N), S.card = t ∧ P S ω) ≤ _
  rw [hevent]
  have hprob (S : Finset (Fin N)) (hS : S ∈ I) :
      uniformProbability (P S) = (1 - 1 / (q : ℝ)) ^ (t.choose 2) := by
    have hcard : S.card = t := Finset.mem_powersetCard_univ.mp hS
    simpa only [P, hcard] using probability_fixed_independent_set hq S
  have hcard : (I.card : ℝ) ≤ (2 : ℝ) ^ N := by
    have hnat : I.card ≤ 2 ^ N := by
      simpa only [Fintype.card_finset, Fintype.card_fin] using Finset.card_le_univ I
    exact_mod_cast hnat
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (Nat.succ_le_iff.mpr hq)
  have hbase : 0 ≤ 1 - 1 / (q : ℝ) := by
    have hdiv : 1 / (q : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hqR
    linarith
  calc
    _ ≤ ∑ S ∈ I, uniformProbability (P S) := uniformProbability_exists_le I P
    _ = (I.card : ℝ) * (1 - 1 / (q : ℝ)) ^ (t.choose 2) := by
      rw [Finset.sum_congr rfl hprob]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (pow_nonneg hbase _)

end HighGirth



/- Component: FinalAssembly.lean -/
set_option autoImplicit false
open scoped BigOperators

namespace HighGirth

/- Assembly fragment: concatenate the checked Alteration, NumericBounds,
GraphEvents, ProbabilityBounds and RandomGraphBounds components before this
file. This fragment supplies no replacements for their definitions or proofs. -/

/-- The strict real half-budget selects an actual graph to which deterministic
alteration applies. The two probabilistic bounds are the only internal inputs. -/
theorem high_girth_of_graph_bounds {N q k t : ℕ} (hq : 0 < q)
    (hN : 0 < N) (hbalance : N = 2 * k * t)
    (hmean : uniformMean (fun ω : Sym2 (Fin N) → Fin q =>
        ((shortCycles (sampleGraph hq ω) k).card : ℝ)) ≤ (N : ℝ) / 4)
    (hbad : uniformProbability (fun ω : Sym2 (Fin N) → Fin q =>
        ∃ S : Finset (Fin N), S.card = t ∧
          ∀ u ∈ S, ∀ v ∈ S, ¬ (sampleGraph hq ω).Adj u v) < 1 / 4) :
    ∃ M : ℕ, ∃ H : SimpleGraph (Fin M), ¬ BookSixth.HasColoring H k ∧
      ∀ l : ℕ, l ≤ k → ¬ BookSixth.HasCycle H l := by
  classical
  letI : Nonempty (Sym2 (Fin N) → Fin q) := ⟨fun _ => ⟨0, hq⟩⟩
  obtain ⟨ω, hnot, hshort⟩ := exists_good_outcome
    (fun ω : Sym2 (Fin N) → Fin q => (shortCycles (sampleGraph hq ω) k).card)
    (fun ω : Sym2 (Fin N) → Fin q =>
      ∃ S : Finset (Fin N), S.card = t ∧
        ∀ u ∈ S, ∀ v ∈ S, ¬ (sampleGraph hq ω).Adj u v)
    (N : ℝ) (by exact_mod_cast hN) hmean hbad
  apply alteration (k := k) (t := t) (sampleGraph hq ω)
  · intro S hS
    apply (not_independent_iff_edge (sampleGraph hq ω) S).mp
    exact fun hi => hnot ⟨S, hS, hi⟩
  · have htwice : 2 * (shortCycles (sampleGraph hq ω) k).card < N := by
      have hreal : (2 : ℝ) * (shortCycles (sampleGraph hq ω) k).card < (N : ℝ) := by
        linarith
      exact_mod_cast hreal
    have hbound : k * (t - 1) ≤ k * t := Nat.mul_le_mul_left k (Nat.sub_le t 1)
    have hbalance' : 2 * (k * t) = N := by
      simpa only [mul_assoc] using hbalance.symm
    omega

/-- The explicit parameters discharge both probabilistic inputs and the exact
vertex-count balance; there are no unproved graph or probability premises. -/
theorem high_girth_chromatic (k : ℕ) (hk : 2 ≤ k) :
    ∃ N : ℕ, ∃ G : SimpleGraph (Fin N), ¬ BookSixth.HasColoring G k ∧
      ∀ l : ℕ, l ≤ k → ¬ BookSixth.HasCycle G l := by
  have hp := parameters k hk
  have hq : 0 < colorCount k := lt_of_lt_of_le Nat.zero_lt_one hp.1
  have hN : 0 < vertexCount k := lt_of_lt_of_le Nat.zero_lt_one hp.2.2.1
  apply high_girth_of_graph_bounds (N := vertexCount k) (q := colorCount k)
    (k := k) (t := independentSize k) hq hN hp.2.2.2.1
  · exact (mean_shortCycles_le hq k).trans (short_cycle_expectation_bound k hk)
  · exact (probability_independent_set_le hq (independentSize k)).trans_lt
      (independent_union_bound k hk)

end HighGirth

open BookSixth

theorem solution (k : ℕ) (hk : 2 ≤ k) :
    ∃ N : ℕ, ∃ G : SimpleGraph (Fin N), ¬ HasColoring G k ∧
      ∀ l : ℕ, l ≤ k → ¬ HasCycle G l := by
  exact HighGirth.high_girth_chromatic k hk

#print axioms solution
