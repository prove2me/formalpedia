-- Prove2me | solution 1 for BenchmarkComparisons.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T09:14:45.425124+00:00
-- url     : https://prove2.me/submissions/7c156fee-ef6e-4d69-8dc0-e56fe94874d4

import Definitions.Def_BenchmarkRelations
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.OfFn
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.Filter.CountableInter
import Mathlib.Probability.CDF
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Bases
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.OpenPartialHomeomorph.Basic


/- Whole source module: CountableBorelColoring -/
namespace BenchmarkCountableProof
section Source0
/-! A countable Borel coloring for a finite family of Borel neighbor maps.
It is constructed from a Borel injection into Cantor space by taking the
first binary prefix that distinguishes the point from its distinct neighbors.
-/

noncomputable section

open Set

namespace BenchmarkCountableColoring

variable {X : Type*} (d : ℕ) (nb : Fin d → X → X) (code : X → ℕ → Bool)
  (hinj : Function.Injective code)

def distinguishes (x : X) (n : ℕ) : Prop :=
  ∀ i : Fin d, nb i x = x ∨ ∃ j : Fin n, code (nb i x) j ≠ code x j

include hinj

lemma exists_distinguishes (x : X) : ∃ n, distinguishes d nb code x n := by
  classical
  have hex : ∀ i : Fin d, ∃ n, nb i x = x ∨
      ∃ j : Fin n, code (nb i x) j ≠ code x j := by
    intro i
    by_cases hix : nb i x = x
    · exact ⟨0, Or.inl hix⟩
    · have hne : code (nb i x) ≠ code x := fun h => hix (hinj h)
      have : ∃ j : ℕ, code (nb i x) j ≠ code x j := by
        by_contra h
        push Not at h
        exact hne (funext h)
      obtain ⟨j, hj⟩ := this
      exact ⟨j + 1, Or.inr ⟨⟨j, by omega⟩, hj⟩⟩
  choose b hb using hex
  refine ⟨∑ i, b i, fun i => ?_⟩
  rcases hb i with h | ⟨j, hj⟩
  · exact Or.inl h
  · have hle : b i ≤ ∑ a, b a := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact Or.inr ⟨⟨j, lt_of_lt_of_le j.isLt hle⟩, hj⟩

def prefixLength (x : X) : ℕ := by
  classical
  exact Nat.find (exists_distinguishes d nb code hinj x)

lemma prefixLength_spec (x : X) :
    distinguishes d nb code x (prefixLength d nb code hinj x) := by
  classical
  exact Nat.find_spec (exists_distinguishes d nb code hinj x)

def countColor (x : X) : ℕ :=
  Nat.pair (prefixLength d nb code hinj x)
    (Encodable.encode (List.ofFn (fun j : Fin (prefixLength d nb code hinj x) => code x j)))

theorem countColor_proper (G : SimpleGraph X)
    (henum : ∀ x y, G.Adj x y → ∃ i, nb i x = y) :
    ∀ x y, G.Adj x y → countColor d nb code hinj x ≠ countColor d nb code hinj y := by
  intro x y hxy heq
  obtain ⟨i, hi⟩ := henum x y hxy
  have hp := prefixLength_spec d nb code hinj x i
  rw [hi] at hp
  rcases hp with hsame | ⟨j, hj⟩
  · exact hxy.ne hsame.symm
  · have hpair := Nat.pair_eq_pair.mp heq
    have hlen := hpair.1
    have hlist := Encodable.encode_injective hpair.2
    rw [← hlen] at hlist
    have hfun := List.ofFn_injective hlist
    have he := congrFun hfun j
    exact hj he.symm

variable [MeasurableSpace X]

theorem measurable_prefixLength
    (hnb : ∀ i, Measurable (nb i)) (hcode : Measurable code) :
    Measurable (prefixLength d nb code hinj) := by
  classical
  apply measurable_find
  intro n
  change MeasurableSet {x | ∀ i : Fin d, nb i x = x ∨
    ∃ j : Fin n, code (nb i x) j ≠ code x j}
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have heq : MeasurableSet {x | nb i x = x} := by
    have he : MeasurableSet {x | code (nb i x) = code x} :=
      measurableSet_eq_fun (hcode.comp (hnb i)) hcode
    simpa only [hinj.eq_iff] using he
  have hneq : ∀ j : Fin n, MeasurableSet {x | code (nb i x) j ≠ code x j} := by
    intro j
    exact (measurableSet_eq_fun ((measurable_pi_apply (j : ℕ)).comp (hcode.comp (hnb i)))
      ((measurable_pi_apply (j : ℕ)).comp hcode)).compl
  simpa only [setOf_or, setOf_exists] using heq.union (MeasurableSet.iUnion hneq)

theorem measurable_countColor
    (hnb : ∀ i, Measurable (nb i)) (hcode : Measurable code) :
    Measurable (countColor d nb code hinj) := by
  have hm : Measurable (fun p : X × ℕ =>
      Nat.pair p.2 (Encodable.encode (List.ofFn (fun j : Fin p.2 => code p.1 j)))) := by
    apply measurable_from_prod_countable_left
    intro n
    have hp : Measurable (fun x => fun j : Fin n => code x j) :=
      measurable_pi_lambda _ (fun j => (measurable_pi_apply (j : ℕ)).comp hcode)
    exact (measurable_of_countable (fun f : Fin n → Bool =>
      Nat.pair n (Encodable.encode (List.ofFn f)))).comp hp
  exact hm.comp (measurable_id.prodMk (measurable_prefixLength d nb code hinj hnb hcode))

theorem exists_measurable_countable_proper_coloring (G : SimpleGraph X)
    (henum : ∀ x y, G.Adj x y → ∃ i, nb i x = y)
    (hnb : ∀ i, Measurable (nb i)) (hcode : Measurable code) :
    ∃ c : X → ℕ, Measurable c ∧ ∀ x y, G.Adj x y → c x ≠ c y :=
  ⟨countColor d nb code hinj, measurable_countColor d nb code hinj hnb hcode,
    countColor_proper d nb code hinj G henum⟩

end BenchmarkCountableColoring
end
end Source0
end BenchmarkCountableProof

/- Whole source module: FiniteBorelColoring -/
namespace BenchmarkCountableProof
section Source1
/-! A Borel greedy finite coloring, from an explicitly enumerated finite
neighbor family and a countable Borel proper coloring. This supplies the
finite-coloring step needed by the graph-distance block construction. -/

noncomputable section

namespace BenchmarkFiniteColoring

lemma exists_missing (d : ℕ) (a : Fin d → Fin (d + 1)) :
    ∃ c : Fin (d + 1), ∀ i, c ≠ a i := by
  classical
  have hns : ¬ Function.Surjective a := by
    intro hs
    have hcard := Fintype.card_le_of_surjective a hs
    simp only [Fintype.card_fin] at hcard
    omega
  simp only [Function.Surjective, not_forall, not_exists] at hns
  obtain ⟨c, hc⟩ := hns
  exact ⟨c, fun i h => hc i h.symm⟩

def missing (d : ℕ) (a : Fin d → Fin (d + 1)) : Fin (d + 1) :=
  Classical.choose (exists_missing d a)

lemma missing_ne (d : ℕ) (a : Fin d → Fin (d + 1)) (i : Fin d) :
    missing d a ≠ a i := (Classical.choose_spec (exists_missing d a)) i

variable {X : Type*} (d : ℕ) (nb : Fin d → X → X) (rank : X → ℕ)

def stage : ℕ → X → Fin (d + 1)
  | 0 => fun _ => 0
  | n + 1 => fun x => if rank x = n then
      missing d (fun i => stage n (nb i x)) else stage n x

def finiteColor (x : X) : Fin (d + 1) := stage d nb rank (rank x + 1) x

lemma stage_stable (x : X) (n : ℕ) (hn : rank x + 1 ≤ n) :
    stage d nb rank n x = finiteColor d nb rank x := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      have hne : rank x ≠ n := by omega
      simpa only [stage, if_neg hne] using ih

lemma finiteColor_eq_missing (x : X) :
    finiteColor d nb rank x =
      missing d (fun i => stage d nb rank (rank x) (nb i x)) := by
  simp [finiteColor, stage]

theorem finiteColor_ne_of_rank_lt (G : SimpleGraph X)
    (henum : ∀ x y, G.Adj x y → ∃ i, nb i x = y)
    {x y : X} (hxy : G.Adj x y) (hrank : rank x < rank y) :
    finiteColor d nb rank x ≠ finiteColor d nb rank y := by
  obtain ⟨i, hi⟩ := henum y x hxy.symm
  intro heq
  have hneq := missing_ne d (fun j => stage d nb rank (rank y) (nb j y)) i
  rw [hi, stage_stable d nb rank x (rank y) (by omega)] at hneq
  rw [← finiteColor_eq_missing] at hneq
  exact hneq heq.symm

theorem finiteColor_proper (G : SimpleGraph X)
    (henum : ∀ x y, G.Adj x y → ∃ i, nb i x = y)
    (hproper : ∀ x y, G.Adj x y → rank x ≠ rank y) :
    ∀ x y, G.Adj x y → finiteColor d nb rank x ≠ finiteColor d nb rank y := by
  intro x y hxy
  rcases lt_or_gt_of_ne (hproper x y hxy) with hr | hr
  · exact finiteColor_ne_of_rank_lt d nb rank G henum hxy hr
  · exact (finiteColor_ne_of_rank_lt d nb rank G henum hxy.symm hr).symm

variable [MeasurableSpace X]

theorem measurable_stage
    (hnb : ∀ i, Measurable (nb i)) (hrank : Measurable rank) :
    ∀ n, Measurable (stage d nb rank n) := by
  classical
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hm : Measurable (fun x => missing d (fun i => stage d nb rank n (nb i x))) := by
        have ht : Measurable (fun x => fun i => stage d nb rank n (nb i x)) :=
          measurable_pi_lambda _ (fun i => ih.comp (hnb i))
        exact (measurable_of_countable (f := missing d)).comp ht
      exact hm.ite (measurableSet_eq_fun hrank measurable_const) ih

theorem measurable_finiteColor
    (hnb : ∀ i, Measurable (nb i)) (hrank : Measurable rank) :
    Measurable (finiteColor d nb rank) := by
  have hm : Measurable (fun p : ℕ × X => stage d nb rank p.1 p.2) :=
    measurable_from_prod_countable_right (measurable_stage d nb rank hnb hrank)
  exact hm.comp ((hrank.add_const 1).prodMk measurable_id)

theorem exists_measurable_finite_proper_coloring (G : SimpleGraph X)
    (henum : ∀ x y, G.Adj x y → ∃ i, nb i x = y)
    (hnb : ∀ i, Measurable (nb i)) (hrank : Measurable rank)
    (hproper : ∀ x y, G.Adj x y → rank x ≠ rank y) :
    ∃ c : X → Fin (d + 1), Measurable c ∧ ∀ x y, G.Adj x y → c x ≠ c y :=
  ⟨finiteColor d nb rank, measurable_finiteColor d nb rank hnb hrank,
    finiteColor_proper d nb rank G henum hproper⟩

end BenchmarkFiniteColoring
end
end Source1
end BenchmarkCountableProof

/- Whole source module: GraphDistanceBlocks -/
namespace BenchmarkCountableProof
section Source2
/-!
# The graph-distance block construction

This is the constructive part of Benchmark.tex, Theorem 3.1.  It proves an
actual Borel reduction to the usual null-difference relation, once the
finite refining separated Borel partitions and Borel bounded neighborhoods
have been supplied.  It does not claim to prove the Borel finite-coloring
theorem or instantiate those partitions on the full free-group shift.

The code uses a capped integer minimum, rather than extended real distance.
This makes the coordinates measurable from the Borel neighborhood sets.
-/

open Filter Set
open scoped Topology

noncomputable section

namespace BenchmarkGraphBlocks

variable {X : Type*} (G : SimpleGraph X) (k : ℕ → ℕ)
  (color : ∀ n, X → Fin (k n))

def nearCell (n : ℕ) (i : Fin (k n)) (x : X) (r : ℕ) : Prop :=
  ∃ z, G.Reachable x z ∧ G.dist x z ≤ r ∧ color n z = i

lemma capped_exists (n : ℕ) (i : Fin (k n)) (x : X) :
    ∃ r, r = n + 1 ∨ nearCell G k color n i x r :=
  ⟨n + 1, Or.inl rfl⟩

def cappedDistance (n : ℕ) (i : Fin (k n)) (x : X) : ℕ :=
  by classical exact Nat.find (capped_exists G k color n i x)

lemma cappedDistance_le (n : ℕ) (i : Fin (k n)) (x : X) :
    cappedDistance G k color n i x ≤ n + 1 := by
  classical
  exact Nat.find_min' (capped_exists G k color n i x) (Or.inl rfl)

lemma cappedDistance_spec (n : ℕ) (i : Fin (k n)) (x : X) :
    cappedDistance G k color n i x = n + 1 ∨
      nearCell G k color n i x (cappedDistance G k color n i x) := by
  classical
  exact Nat.find_spec (capped_exists G k color n i x)

lemma cappedDistance_self (n : ℕ) (x : X) :
    cappedDistance G k color n (color n x) x = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  apply Nat.find_min'
  exact Or.inr ⟨x, SimpleGraph.Reachable.rfl, by simp, rfl⟩

lemma cappedDistance_le_add (n : ℕ) (i : Fin (k n))
    {x y : X} (hxy : G.Reachable x y) :
    cappedDistance G k color n i x ≤
      cappedDistance G k color n i y + G.dist x y := by
  classical
  rcases cappedDistance_spec G k color n i y with hcap | ⟨z, hyz, hdist, hcol⟩
  · calc
      cappedDistance G k color n i x ≤ n + 1 := cappedDistance_le G k color n i x
      _ ≤ cappedDistance G k color n i y + G.dist x y := by omega
  · apply Nat.find_min'
    refine Or.inr ⟨z, hxy.trans hyz, ?_, hcol⟩
    have ht := hxy.dist_triangle_left z
    omega

def coordinate (n : ℕ) (i : Fin (k n)) (x : X) : ℝ :=
  1 - (cappedDistance G k color n i x : ℝ) / ((n : ℝ) + 1)

lemma coordinate_nonneg (n : ℕ) (i : Fin (k n)) (x : X) :
    0 ≤ coordinate G k color n i x := by
  have hd : (cappedDistance G k color n i x : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast cappedDistance_le G k color n i x
  have hp : 0 < (n : ℝ) + 1 := by positivity
  unfold coordinate
  exact sub_nonneg.mpr ((div_le_one hp).mpr hd)

lemma coordinate_le_one (n : ℕ) (i : Fin (k n)) (x : X) :
    coordinate G k color n i x ≤ 1 := by
  unfold coordinate
  have : 0 ≤ (cappedDistance G k color n i x : ℝ) / ((n : ℝ) + 1) := by positivity
  linarith

lemma coordinate_self (n : ℕ) (x : X) :
    coordinate G k color n (color n x) x = 1 := by
  simp [coordinate, cappedDistance_self]

lemma coordinate_pos_witness (n : ℕ) (i : Fin (k n)) (x : X)
    (hp : 0 < coordinate G k color n i x) :
    ∃ z, G.Reachable x z ∧ G.dist x z ≤ n ∧ color n z = i := by
  rcases cappedDistance_spec G k color n i x with hcap | ⟨z, hxz, hd, hc⟩
  · have : coordinate G k color n i x = 0 := by
      simp [coordinate, hcap, Nat.cast_add, Nat.cast_one,
        ne_of_gt (by positivity : 0 < (n : ℝ) + 1)]
    linarith
  · refine ⟨z, hxz, ?_, hc⟩
    have hne : cappedDistance G k color n i x ≠ n + 1 := by
      intro hcap
      have : coordinate G k color n i x = 0 := by
        simp [coordinate, hcap, Nat.cast_add, Nat.cast_one,
          ne_of_gt (by positivity : 0 < (n : ℝ) + 1)]
      linarith
    have hb := cappedDistance_le G k color n i x
    omega

lemma coordinate_difference_le (n : ℕ) (i : Fin (k n))
    {x y : X} (hxy : G.Reachable x y) :
    |coordinate G k color n i x - coordinate G k color n i y| ≤
      (G.dist x y : ℝ) / ((n : ℝ) + 1) := by
  have hp : 0 < (n : ℝ) + 1 := by positivity
  have h₁ : (cappedDistance G k color n i x : ℝ) ≤
      (cappedDistance G k color n i y : ℝ) + (G.dist x y : ℝ) := by
    exact_mod_cast cappedDistance_le_add G k color n i hxy
  have h₂ : (cappedDistance G k color n i y : ℝ) ≤
      (cappedDistance G k color n i x : ℝ) + (G.dist x y : ℝ) := by
    have h := cappedDistance_le_add G k color n i hxy.symm
    rw [SimpleGraph.dist_comm (G := G) (u := y) (v := x)] at h
    exact_mod_cast h
  have habs : |(cappedDistance G k color n i x : ℝ) -
      (cappedDistance G k color n i y : ℝ)| ≤ (G.dist x y : ℝ) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  unfold coordinate
  have heq : (1 - (cappedDistance G k color n i x : ℝ) / ((n : ℝ) + 1)) -
      (1 - (cappedDistance G k color n i y : ℝ) / ((n : ℝ) + 1)) =
      -((cappedDistance G k color n i x : ℝ) -
        (cappedDistance G k color n i y : ℝ)) / ((n : ℝ) + 1) := by ring
  rw [heq, abs_div, abs_neg, abs_of_pos hp]
  exact div_le_div_of_nonneg_right habs hp.le

def code (x : X) (j : ℕ) : ℝ :=
  if h : (Nat.unpair j).2 < k (Nat.unpair j).1 then
    coordinate G k color (Nat.unpair j).1 ⟨(Nat.unpair j).2, h⟩ x else 0

lemma code_pair (x : X) (n : ℕ) (i : Fin (k n)) :
    code G k color x (Nat.pair n i.val) = coordinate G k color n i x := by
  unfold code
  rw [Nat.unpair_pair]
  rw [dif_pos i.isLt]

lemma reachable_implies_null {x y : X} (hxy : G.Reachable x y) :
    Tendsto (fun j => code G k color x j - code G k color y j) atTop (𝓝 0) := by
  classical
  have hlim : Tendsto (fun n : ℕ => (G.dist x y : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, one_mul] using
      (tendsto_const_nhds (x := (G.dist x y : ℝ))).mul
        tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Metric.tendsto_atTop] at hlim ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hlim ε hε
  let s : Finset (ℕ × ℕ) := (Finset.range N).biUnion fun n =>
    (Finset.range (k n)).image (fun i => (n, i))
  let t : Finset ℕ := s.image (fun p => Nat.pair p.1 p.2)
  refine ⟨t.sup id + 1, fun j hj => ?_⟩
  unfold code
  split_ifs with hi
  · have hn : N ≤ (Nat.unpair j).1 := by
      by_contra hh
      have hs : Nat.unpair j ∈ s := by
        apply Finset.mem_biUnion.mpr
        refine ⟨(Nat.unpair j).1, Finset.mem_range.mpr (by omega), ?_⟩
        exact Finset.mem_image.mpr
          ⟨(Nat.unpair j).2, Finset.mem_range.mpr hi, by simp⟩
      have ht : j ∈ t := Finset.mem_image.mpr ⟨Nat.unpair j, hs, Nat.pair_unpair j⟩
      have hsup : j ≤ t.sup id := Finset.le_sup (f := id) ht
      omega
    have hb := coordinate_difference_le G k color (Nat.unpair j).1
      ⟨(Nat.unpair j).2, hi⟩ hxy
    have hl := hN (Nat.unpair j).1 hn
    simp only [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity :
      0 ≤ (G.dist x y : ℝ) / ((Nat.unpair j).1 + 1))] at hl
    simpa only [Real.dist_eq, sub_zero] using lt_of_le_of_lt hb hl
  · simpa using hε

/-- The inverse direction of the graph-distance construction. The separation
radius is `4(n+1)` to permit witnesses at integer distance at most `n`. -/
theorem null_iff_reachable
    (hrefine : ∀ n x y, color (n + 1) x = color (n + 1) y → color n x = color n y)
    (hseparate : ∀ x y, (∀ n, color n x = color n y) → x = y)
    (hfar : ∀ n x y, color n x = color n y → G.Reachable x y →
      G.dist x y ≤ 4 * (n + 1) → x = y)
    (x y : X) :
    Tendsto (fun j => code G k color x j - code G k color y j) atTop (𝓝 0) ↔
      G.Reachable x y := by
  classical
  constructor
  · intro h
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h) (1 / 4) (by norm_num)
    have hex : ∀ n, N ≤ n → ∃ z, G.Reachable y z ∧ G.dist y z ≤ n ∧
        color n z = color n x := by
      intro n hn
      have hc := hN (Nat.pair n (color n x).val)
        (le_trans hn (Nat.left_le_pair _ _))
      rw [code_pair, code_pair, coordinate_self, Real.dist_eq, sub_zero] at hc
      apply coordinate_pos_witness G k color n (color n x) y
      have hh := (abs_lt.mp hc).2
      linarith
    choose z hz using hex
    have hstep : ∀ n (hn : N ≤ n), z n hn = z (n + 1) (by omega) := by
      intro n hn
      apply hfar n
      · exact (hz n hn).2.2.trans
          (hrefine n _ _ (hz (n + 1) (by omega)).2.2).symm
      · exact (hz n hn).1.symm.trans (hz (n + 1) (by omega)).1
      · have ht := ((hz n hn).1.symm).dist_triangle_left (z (n + 1) (by omega))
        rw [SimpleGraph.dist_comm (G := G) (u := z n hn) (v := y)] at ht
        have ha := (hz n hn).2.1
        have hb := (hz (n + 1) (by omega)).2.1
        omega
    have hconst : ∀ n (hn : N ≤ n), z n hn = z N le_rfl := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => rfl
      | succ n hn ih => exact (hstep n hn).symm.trans ih
    have hback : ∀ a b, a ≤ b → ∀ u v,
        color b u = color b v → color a u = color a v := by
      intro a b hab u v hc
      induction b, hab using Nat.le_induction with
      | base => exact hc
      | succ b hab ih => exact ih (hrefine b u v hc)
    have heq : z N le_rfl = x := by
      apply hseparate
      intro n
      have hn : N ≤ max N n := le_max_left _ _
      have hc := (hz (max N n) hn).2.2
      rw [hconst (max N n) hn] at hc
      exact hback n (max N n) (le_max_right _ _) _ _ hc
    exact ((hz N le_rfl).1.trans (heq ▸ SimpleGraph.Reachable.rfl)).symm
  · exact reachable_implies_null G k color

variable [MeasurableSpace X]

theorem measurable_coordinate
    (hnear : ∀ n (i : Fin (k n)) r, MeasurableSet {x | nearCell G k color n i x r})
    (n : ℕ) (i : Fin (k n)) : Measurable (coordinate G k color n i) := by
  classical
  have hd : Measurable (cappedDistance G k color n i) := by
    apply measurable_find
    intro r
    by_cases hr : r = n + 1
    · simp only [hr, true_or, setOf_true]
      exact MeasurableSet.univ
    · simpa only [hr, false_or] using hnear n i r
  have hc : Measurable (fun x => (cappedDistance G k color n i x : ℝ)) :=
    (measurable_from_nat : Measurable (fun a : ℕ => (a : ℝ))).comp hd
  exact measurable_const.sub (hc.div_const _)

theorem measurable_code
    (hnear : ∀ n (i : Fin (k n)) r, MeasurableSet {x | nearCell G k color n i x r}) :
    Measurable (code G k color) := by
  classical
  apply measurable_pi_lambda
  intro j
  unfold code
  split_ifs
  · exact measurable_coordinate G k color hnear _ _
  · exact measurable_const

theorem exists_borel_null_reduction
    (hrefine : ∀ n x y, color (n + 1) x = color (n + 1) y → color n x = color n y)
    (hseparate : ∀ x y, (∀ n, color n x = color n y) → x = y)
    (hfar : ∀ n x y, color n x = color n y → G.Reachable x y →
      G.dist x y ≤ 4 * (n + 1) → x = y)
    (hnear : ∀ n (i : Fin (k n)) r, MeasurableSet {x | nearCell G k color n i x r}) :
    ∃ F : X → (ℕ → ℝ), Measurable F ∧
      (∀ x j, 0 ≤ F x j ∧ F x j ≤ 1) ∧
      ∀ x y, G.Reachable x y ↔
        Tendsto (fun j => F x j - F y j) atTop (𝓝 0) := by
  classical
  refine ⟨code G k color, measurable_code G k color hnear, ?_, ?_⟩
  · intro x j
    unfold code
    split_ifs
    · exact ⟨coordinate_nonneg G k color _ _ _, coordinate_le_one G k color _ _ _⟩
    · norm_num
  · intro x y
    exact (null_iff_reachable G k color hrefine hseparate hfar x y).symm

end BenchmarkGraphBlocks
end
end Source2
end BenchmarkCountableProof

/- Whole source module: RefiningFinitePartitions -/
namespace BenchmarkCountableProof
section Source3
/-! Finite proper colorings of graph powers are refined into nested finite
partitions that also separate all points. Bounded-ball enumerators supply
the measurable bounded-neighborhood hypothesis in the block construction. -/

open Filter Set
open scoped Topology

noncomputable section

namespace BenchmarkRefiningPartitions

variable {X : Type*} (qk : ℕ → ℕ) (q : ∀ n, X → Fin (qk n))
  (embedding : X → ℕ → Bool)

abbrev RawColor (n : ℕ) :=
  (Fin (n + 1) → Bool) × (∀ i : Fin (n + 1), Fin (qk i))

def colorSize (n : ℕ) : ℕ := Fintype.card (RawColor qk n)

def rawColor (n : ℕ) (x : X) : RawColor qk n :=
  (fun i => embedding x i, fun i => q i x)

def color (n : ℕ) (x : X) : Fin (colorSize qk n) :=
  Fintype.equivFin (RawColor qk n) (rawColor qk q embedding n x)

lemma rawColor_eq_of_color_eq {n : ℕ} {x y : X}
    (h : color qk q embedding n x = color qk q embedding n y) :
    rawColor qk q embedding n x = rawColor qk q embedding n y :=
  (Fintype.equivFin (RawColor qk n)).injective h

theorem color_refines (n : ℕ) (x y : X)
    (h : color qk q embedding (n + 1) x = color qk q embedding (n + 1) y) :
    color qk q embedding n x = color qk q embedding n y := by
  apply congrArg (Fintype.equivFin (RawColor qk n))
  have hr := rawColor_eq_of_color_eq qk q embedding h
  apply Prod.ext
  · funext i
    exact congrArg (fun c : RawColor qk (n + 1) => c.1 ⟨i, by omega⟩) hr
  · funext i
    exact congrArg (fun c : RawColor qk (n + 1) => c.2 ⟨i, by omega⟩) hr

theorem color_separates (hinj : Function.Injective embedding) (x y : X)
    (h : ∀ n, color qk q embedding n x = color qk q embedding n y) : x = y := by
  apply hinj
  funext n
  have hr := rawColor_eq_of_color_eq qk q embedding (h n)
  exact congrArg (fun c : RawColor qk n => c.1 ⟨n, by omega⟩) hr

theorem color_equal_implies_q_equal (n : ℕ) (x y : X)
    (h : color qk q embedding n x = color qk q embedding n y) : q n x = q n y := by
  have hr := rawColor_eq_of_color_eq qk q embedding h
  exact congrArg (fun c : RawColor qk n => c.2 ⟨n, by omega⟩) hr

variable [MeasurableSpace X]

theorem measurable_color (hq : ∀ n, Measurable (q n)) (he : Measurable embedding) (n : ℕ) :
    Measurable (color qk q embedding n) := by
  have hprefix : Measurable (fun x => fun i : Fin (n + 1) => embedding x i) :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply (i : ℕ)).comp he)
  have hcolors : Measurable (fun x => fun i : Fin (n + 1) => q i x) :=
    measurable_pi_lambda _ (fun i => hq i)
  have hraw : Measurable (rawColor qk q embedding n) := hprefix.prodMk hcolors
  exact (measurable_of_countable (Fintype.equivFin (RawColor qk n))).comp hraw

theorem measurable_nearCell (G : SimpleGraph X) (m : ℕ → ℕ)
    (ball : ∀ r, Fin (m r) → X → X)
    (hball_meas : ∀ r i, Measurable (ball r i))
    (hball : ∀ r x z, (G.Reachable x z ∧ G.dist x z ≤ r) ↔ ∃ i, ball r i x = z)
    (hq : ∀ n, Measurable (q n)) (he : Measurable embedding)
    (n : ℕ) (i : Fin (colorSize qk n)) (r : ℕ) :
    MeasurableSet {x | BenchmarkGraphBlocks.nearCell G (colorSize qk)
      (color qk q embedding) n i x r} := by
  have heq : {x | BenchmarkGraphBlocks.nearCell G (colorSize qk)
      (color qk q embedding) n i x r} =
      ⋃ j : Fin (m r), {x | color qk q embedding n (ball r j x) = i} := by
    ext x
    simp only [BenchmarkGraphBlocks.nearCell, mem_setOf_eq, mem_iUnion]
    constructor
    · rintro ⟨z, hr, hd, hc⟩
      obtain ⟨j, hj⟩ := (hball r x z).mp ⟨hr, hd⟩
      exact ⟨j, hj ▸ hc⟩
    · rintro ⟨j, hj⟩
      have hb := (hball r x (ball r j x)).mpr ⟨j, rfl⟩
      exact ⟨ball r j x, hb.1, hb.2, hj⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro j
  exact ((measurable_color qk q embedding hq he n).comp (hball_meas r j))
    (measurableSet_singleton i)

theorem exists_borel_reduction (G : SimpleGraph X) (m : ℕ → ℕ)
    (ball : ∀ r, Fin (m r) → X → X)
    (hball_meas : ∀ r i, Measurable (ball r i))
    (hball : ∀ r x z, (G.Reachable x z ∧ G.dist x z ≤ r) ↔ ∃ i, ball r i x = z)
    (hq : ∀ n, Measurable (q n)) (he : Measurable embedding)
    (hinj : Function.Injective embedding)
    (hfar : ∀ n x y, q n x = q n y → G.Reachable x y →
      G.dist x y ≤ 4 * (n + 1) → x = y) :
    ∃ F : X → (ℕ → ℝ), Measurable F ∧ (∀ x j, 0 ≤ F x j ∧ F x j ≤ 1) ∧
      ∀ x y, G.Reachable x y ↔ Tendsto (fun j => F x j - F y j) atTop (𝓝 0) := by
  apply BenchmarkGraphBlocks.exists_borel_null_reduction G (colorSize qk) (color qk q embedding)
  · exact color_refines qk q embedding
  · exact color_separates qk q embedding hinj
  · intro n x y hc hr hd
    exact hfar n x y (color_equal_implies_q_equal qk q embedding n x y hc) hr hd
  · exact measurable_nearCell qk q embedding G m ball hball_meas hball hq he

end BenchmarkRefiningPartitions
end
end Source3
end BenchmarkCountableProof

/- Whole source module: BoundedGraphNull -/
namespace BenchmarkCountableProof
section Source4
/-! The complete graph-distance construction for graphs whose bounded balls
are explicitly enumerated by finitely many measurable maps. No finite Borel
coloring theorem is assumed: the prefix and greedy constructions supply it.
-/

open Filter Set
open scoped Topology

noncomputable section

namespace BenchmarkBoundedGraphNull

variable {X : Type*} (G : SimpleGraph X)

def distancePower (r : ℕ) : SimpleGraph X where
  Adj x y := x ≠ y ∧ G.Reachable x y ∧ G.dist x y ≤ r
  symm := by
    intro x y h
    refine ⟨h.1.symm, h.2.1.symm, ?_⟩
    simpa only [SimpleGraph.dist_comm] using h.2.2
  loopless := ⟨by intro x h; exact h.1 rfl⟩

variable [MeasurableSpace X]

theorem exists_borel_reduction
    (m : ℕ → ℕ) (ball : ∀ r, Fin (m r) → X → X)
    (hball_meas : ∀ r i, Measurable (ball r i))
    (hball : ∀ r x z, (G.Reachable x z ∧ G.dist x z ≤ r) ↔ ∃ i, ball r i x = z)
    (embedding : X → ℕ → Bool) (he : Measurable embedding)
    (hinj : Function.Injective embedding) :
    ∃ F : X → (ℕ → ℝ), Measurable F ∧ (∀ x j, 0 ≤ F x j ∧ F x j ≤ 1) ∧
      ∀ x y, G.Reachable x y ↔ Tendsto (fun j => F x j - F y j) atTop (𝓝 0) := by
  classical
  have hex : ∀ n : ℕ, ∃ q : X → Fin (m (4 * (n + 1)) + 1),
      Measurable q ∧ ∀ x y, (distancePower G (4 * (n + 1))).Adj x y → q x ≠ q y := by
    intro n
    let r := 4 * (n + 1)
    let H := distancePower G r
    have henum : ∀ x y, H.Adj x y → ∃ i, ball r i x = y := by
      intro x y hxy
      exact (hball r x y).mp hxy.2
    obtain ⟨rank, hrank, hproper⟩ :=
      BenchmarkCountableColoring.exists_measurable_countable_proper_coloring
        (m r) (ball r) embedding hinj H henum (hball_meas r) he
    exact BenchmarkFiniteColoring.exists_measurable_finite_proper_coloring
      (m r) (ball r) rank H henum (hball_meas r) hrank hproper
  choose q hq hproper using hex
  apply BenchmarkRefiningPartitions.exists_borel_reduction
    (fun n => m (4 * (n + 1)) + 1) q embedding G m ball hball_meas hball hq he hinj
  intro n x y hc hr hd
  by_contra hne
  exact hproper n x y ⟨hne, hr, hd⟩ hc

end BenchmarkBoundedGraphNull
end
end Source4
end BenchmarkCountableProof

/- Whole source module: ShiftGraph -/
namespace BenchmarkCountableProof
section Source5
/-! The full binary free-group shift and its four-generator Borel graph.
The full shift is used, including points with stabilizers. -/

open Filter Set
open scoped Topology

noncomputable section

namespace BenchmarkShift

abbrev Group := FreeGroup (Fin 2)
abbrev Point := Group → Bool
abbrev Letter := Fin 2 × Bool
abbrev Alphabet := Option Letter

def shift (g : Group) (x : Point) : Point := fun h => x (g⁻¹ * h)

@[simp] lemma shift_one (x : Point) : shift 1 x = x := by ext h; simp [shift]

lemma shift_mul (g h : Group) (x : Point) : shift g (shift h x) = shift (g * h) x := by
  ext k
  simp only [shift, mul_inv_rev, mul_assoc]

theorem continuous_shift (g : Group) : Continuous (shift g) := by
  apply continuous_pi
  intro h
  exact continuous_apply _

def letterGroup (a : Letter) : Group := if a.2 then FreeGroup.of a.1 else (FreeGroup.of a.1)⁻¹
def reverseLetter (a : Letter) : Letter := (a.1, !a.2)

lemma letterGroup_reverse (a : Letter) : letterGroup (reverseLetter a) = (letterGroup a)⁻¹ := by
  rcases a with ⟨i, b⟩
  cases b <;> simp [letterGroup, reverseLetter]

def graph : SimpleGraph Point where
  Adj x y := x ≠ y ∧ ∃ a : Letter, shift (letterGroup a) x = y
  symm := by
    intro x y h
    obtain ⟨hne, a, ha⟩ := h
    refine ⟨hne.symm, reverseLetter a, ?_⟩
    rw [← ha, letterGroup_reverse, shift_mul, inv_mul_cancel, shift_one]
  loopless := ⟨by intro x h; exact h.1 rfl⟩

lemma reachable_letter (a : Letter) (x : Point) : graph.Reachable x (shift (letterGroup a) x) := by
  by_cases heq : x = shift (letterGroup a) x
  · rw [← heq]
  · exact (show graph.Adj x (shift (letterGroup a) x) from ⟨heq, a, rfl⟩).reachable

theorem reachable_shift (g : Group) : ∀ x : Point, graph.Reachable x (shift g x) := by
  induction g using FreeGroup.induction_on with
  | C1 => intro x; simpa using (SimpleGraph.Reachable.refl (G := graph) x)
  | of i =>
      intro x
      simpa only [letterGroup, if_pos rfl] using reachable_letter (i, true) x
  | inv_of i ih =>
      intro x
      simpa only [letterGroup, Bool.false_eq_true, if_false] using reachable_letter (i, false) x
  | mul g h hg hh =>
      intro x
      exact (hh x).trans (by simpa only [shift_mul] using hg (shift h x))

theorem reachable_iff_shift (x y : Point) : graph.Reachable x y ↔ ∃ g : Group, y = shift g x := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact ⟨1, (shift_one _).symm⟩
    | @cons u v z hadj w ih =>
        obtain ⟨a, ha⟩ := hadj.2
        obtain ⟨g, hg⟩ := ih
        exact ⟨g * letterGroup a, by rw [hg, ← ha, shift_mul]⟩
  · rintro ⟨g, rfl⟩
    exact reachable_shift g x

instance groupCountable : Countable Group := by unfold Group FreeGroup; infer_instance
local instance : Encodable Group := Encodable.ofCountable Group

def cantorCode (x : Point) (n : ℕ) : Bool :=
  match Encodable.decode (α := Group) n with
  | none => false
  | some g => x g

theorem measurable_cantorCode : Measurable cantorCode := by
  apply measurable_pi_lambda
  intro n
  cases hdecode : Encodable.decode (α := Group) n with
  | none => simpa only [cantorCode, hdecode] using (measurable_const : Measurable (fun _ : Point => false))
  | some g => simpa only [cantorCode, hdecode] using (measurable_pi_apply g : Measurable (fun x : Point => x g))

theorem cantorCode_injective : Function.Injective cantorCode := by
  intro x y h
  funext g
  have hc := congrFun h (Encodable.encode g)
  simpa only [cantorCode, Encodable.encodek] using hc

end BenchmarkShift
end
end Source5
end BenchmarkCountableProof

/- Whole source module: ShiftFiniteBalls -/
namespace BenchmarkCountableProof
section Source6
/-! Exact bounded-ball enumeration by padded words over the four signed
generators and the identity. No freeness of the action is assumed. -/

noncomputable section

namespace BenchmarkShift

def step (a : Alphabet) (x : Point) : Point :=
  match a with
  | none => x
  | some b => shift (letterGroup b) x

theorem continuous_step (a : Alphabet) : Continuous (step a) := by
  cases a with
  | none => exact continuous_id
  | some a => exact continuous_shift _

lemma step_reachable_dist (a : Alphabet) (x : Point) :
    graph.Reachable x (step a x) ∧ graph.dist x (step a x) ≤ 1 := by
  cases a with
  | none => exact ⟨SimpleGraph.Reachable.rfl, by simp [step]⟩
  | some a =>
      refine ⟨reachable_letter a x, ?_⟩
      by_cases h : x = shift (letterGroup a) x
      · simp only [step, ← h, SimpleGraph.dist_self, Nat.zero_le]
      · have ha : graph.Adj x (shift (letterGroup a) x) := ⟨h, a, rfl⟩
        exact le_of_eq (SimpleGraph.dist_eq_one_iff_adj.mpr ha)

def wordMap : (r : ℕ) → (Fin r → Alphabet) → Point → Point
  | 0, _, x => x
  | r + 1, w, x => wordMap r (fun i => w i.succ) (step (w 0) x)

theorem continuous_wordMap (r : ℕ) (w : Fin r → Alphabet) : Continuous (wordMap r w) := by
  induction r with
  | zero => exact continuous_id
  | succ r ih => exact (ih (fun i => w i.succ)).comp (continuous_step (w 0))

lemma wordMap_none (r : ℕ) (x : Point) : wordMap r (fun _ => none) x = x := by
  induction r with
  | zero => rfl
  | succ r ih => simpa only [wordMap, step] using ih

lemma wordMap_reachable_dist (r : ℕ) (w : Fin r → Alphabet) (x : Point) :
    graph.Reachable x (wordMap r w x) ∧ graph.dist x (wordMap r w x) ≤ r := by
  induction r generalizing x with
  | zero => exact ⟨SimpleGraph.Reachable.rfl, by simp [wordMap]⟩
  | succ r ih =>
      have hfirst := step_reachable_dist (w 0) x
      have hrest := ih (fun i => w i.succ) (step (w 0) x)
      refine ⟨hfirst.1.trans hrest.1, ?_⟩
      have htri := hfirst.1.dist_triangle_left (wordMap r (fun i => w i.succ) (step (w 0) x))
      change graph.dist x (wordMap r (fun i => w i.succ) (step (w 0) x)) ≤ r + 1
      omega

lemma exists_word_of_distance (r : ℕ) : ∀ x y : Point,
    graph.Reachable x y → graph.dist x y ≤ r → ∃ w : Fin r → Alphabet, wordMap r w x = y := by
  induction r with
  | zero =>
      intro x y hr hd
      have hxy := hr.dist_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hd)
      subst y
      exact ⟨fun i => Fin.elim0 i, rfl⟩
  | succ r ih =>
      intro x y hr hd
      obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_dist
      cases w with
      | nil => exact ⟨fun _ => none, wordMap_none _ _⟩
      | @cons u v z hadj w =>
          obtain ⟨a, ha⟩ := hadj.2
          have hlen : w.length ≤ r := by
            simp only [SimpleGraph.Walk.length_cons] at hw
            omega
          obtain ⟨rest, hrest⟩ := ih v y ⟨w⟩ ((SimpleGraph.dist_le w).trans hlen)
          refine ⟨Fin.cons (some a) rest, ?_⟩
          simpa only [wordMap, Fin.cons_zero, Fin.cons_succ, step, ha] using hrest

def ballSize (r : ℕ) : ℕ := Fintype.card (Fin r → Alphabet)

def ball (r : ℕ) (i : Fin (ballSize r)) : Point → Point :=
  wordMap r ((Fintype.equivFin (Fin r → Alphabet)).symm i)

theorem measurable_ball (r : ℕ) (i : Fin (ballSize r)) : Measurable (ball r i) :=
  (continuous_wordMap r _).measurable

theorem ball_complete (r : ℕ) (x z : Point) :
    (graph.Reachable x z ∧ graph.dist x z ≤ r) ↔ ∃ i, ball r i x = z := by
  constructor
  · rintro ⟨hr, hd⟩
    obtain ⟨w, hw⟩ := exists_word_of_distance r x z hr hd
    refine ⟨Fintype.equivFin (Fin r → Alphabet) w, ?_⟩
    simpa only [ball, Equiv.symm_apply_apply] using hw
  · rintro ⟨i, rfl⟩
    exact wordMap_reachable_dist r _ x

end BenchmarkShift
end
end Source6
end BenchmarkCountableProof

/- Whole source module: BoundedNullProduct -/
namespace BenchmarkCountableProof
section Source7
/-! An explicit product reduction for bounded null-sequence codes. The
boundedness hypothesis is essential: a naive weighted interleaving does
not preserve nullness for arbitrary unbounded arrays. -/

open Filter Set
open scoped Topology

noncomputable section

namespace BenchmarkBoundedNullProduct

def weight (i : ℕ) : ℝ := (1 / 2) ^ i

lemma weight_pos (i : ℕ) : 0 < weight i := by unfold weight; positivity
lemma weight_le_one (i : ℕ) : weight i ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

def code (x : ℕ → ℕ → ℝ) (j : ℕ) : ℝ :=
  weight (Nat.unpair j).1 * x (Nat.unpair j).1 (Nat.unpair j).2

lemma code_pair (x : ℕ → ℕ → ℝ) (i k : ℕ) :
    code x (Nat.pair i k) = weight i * x i k := by simp [code]

theorem continuous_code : Continuous code := by
  apply continuous_pi
  intro j
  exact continuous_const.mul ((continuous_apply _).comp (continuous_apply _))

lemma pair_tendsto (i : ℕ) : Tendsto (Nat.pair i) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  exact eventually_atTop.2 ⟨N, fun k hk => hk.trans (Nat.right_le_pair _ _)⟩

theorem null_iff_rows (x y : ℕ → ℕ → ℝ)
    (hbounded : ∀ i k, |x i k - y i k| ≤ 1) :
    Tendsto (fun j => code x j - code y j) atTop (𝓝 0) ↔
      ∀ i, Tendsto (fun k => x i k - y i k) atTop (𝓝 0) := by
  classical
  constructor
  · intro h i
    have ht := h.comp (pair_tendsto i)
    have hd := ht.div_const (weight i)
    have hne : weight i ≠ 0 := (weight_pos i).ne'
    simpa only [Function.comp_def, code_pair, ← mul_sub, mul_div_cancel_left₀ _ hne,
      zero_div] using hd
  · intro h
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hw : Tendsto weight atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨I, hI⟩ := (Metric.tendsto_atTop.mp hw) ε hε
    have hex : ∀ i : Fin I, ∃ K, ∀ k ≥ K, |x i k - y i k| < ε := by
      intro i
      simpa only [Real.dist_eq, sub_zero] using (Metric.tendsto_atTop.mp (h i)) ε hε
    choose K hK using hex
    let s : Finset (ℕ × ℕ) := (Finset.univ : Finset (Fin I)).biUnion fun i =>
      (Finset.range (K i)).image (fun k => ((i : ℕ), k))
    let t : Finset ℕ := s.image (fun p => Nat.pair p.1 p.2)
    refine ⟨t.sup id + 1, fun j hj => ?_⟩
    let i := (Nat.unpair j).1
    let k := (Nat.unpair j).2
    have heq : code x j - code y j = weight i * (x i k - y i k) := by
      dsimp [code, i, k]
      ring
    rw [Real.dist_eq, sub_zero, heq, abs_mul, abs_of_pos (weight_pos i)]
    by_cases hi : i < I
    · have hk : K ⟨i, hi⟩ ≤ k := by
        by_contra hh
        have hs : (i, k) ∈ s := by
          apply Finset.mem_biUnion.mpr
          refine ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
          exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
        have ht : j ∈ t := by
          apply Finset.mem_image.mpr
          exact ⟨(i, k), hs, Nat.pair_unpair j⟩
        have hsup : j ≤ t.sup id := Finset.le_sup (f := id) ht
        omega
      have hsmall := hK ⟨i, hi⟩ k hk
      exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg _) (weight_le_one i)) hsmall
    · have hsmall := hI i (by omega)
      have hwε : weight i < ε := by
        simpa only [Real.dist_eq, sub_zero, abs_of_pos (weight_pos i)] using hsmall
      calc
        weight i * |x i k - y i k| ≤ weight i :=
          mul_le_of_le_one_right (weight_pos i).le (hbounded i k)
        _ < ε := hwε

theorem exists_product_reduction {X : Type*} [MeasurableSpace X]
    (E : X → X → Prop) (F : X → ℕ → ℝ) (hF : Measurable F)
    (hbounded : ∀ x k, 0 ≤ F x k ∧ F x k ≤ 1)
    (hred : ∀ x y, E x y ↔ Tendsto (fun k => F x k - F y k) atTop (𝓝 0)) :
    ∃ G : (ℕ → X) → (ℕ → ℝ), Measurable G ∧
      (∀ x j, 0 ≤ G x j ∧ G x j ≤ 1) ∧
      ∀ x y, (∀ i, E (x i) (y i)) ↔
        Tendsto (fun j => G x j - G y j) atTop (𝓝 0) := by
  let G := fun x : ℕ → X => code (fun i => F (x i))
  have hrows : Measurable (fun x : ℕ → X => fun i => F (x i)) :=
    measurable_pi_lambda _ (fun i => hF.comp (measurable_pi_apply i))
  refine ⟨G, continuous_code.measurable.comp hrows, ?_, ?_⟩
  · intro x j
    change 0 ≤ weight _ * F (x _) _ ∧ weight _ * F (x _) _ ≤ 1
    exact ⟨mul_nonneg (weight_pos _).le (hbounded _ _).1,
      (mul_le_of_le_one_right (weight_pos _).le (hbounded _ _).2).trans (weight_le_one _)⟩
  · intro x y
    have hb : ∀ i k, |F (x i) k - F (y i) k| ≤ 1 := by
      intro i k
      exact abs_le.mpr ⟨by linarith [(hbounded (x i) k).1, (hbounded (y i) k).2],
        by linarith [(hbounded (x i) k).2, (hbounded (y i) k).1]⟩
    exact (forall_congr' fun i => hred (x i) (y i)).trans (null_iff_rows _ _ hb).symm

end BenchmarkBoundedNullProduct
end
end Source7
end BenchmarkCountableProof

/- Whole source module: ShiftNullReduction -/
namespace BenchmarkCountableProof
section Source8
/-! Actual positive benchmark comparisons: the full F₂ shift orbit
relation, and its countable product, Borel reduce to c₀. -/

open Filter Set
open scoped Topology

noncomputable section

namespace BenchmarkShift

def Orbit (x y : Point) : Prop := ∃ g : Group, ∀ h : Group, y h = x (g⁻¹ * h)

lemma orbit_iff_reachable (x y : Point) : Orbit x y ↔ graph.Reachable x y := by
  rw [reachable_iff_shift]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, funext hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, congrFun hg⟩

theorem exists_borel_shift_null_reduction :
    ∃ F : Point → (ℕ → ℝ), Measurable F ∧ (∀ x j, 0 ≤ F x j ∧ F x j ≤ 1) ∧
      ∀ x y, Orbit x y ↔ Tendsto (fun j => F x j - F y j) atTop (𝓝 0) := by
  obtain ⟨F, hF, hb, hr⟩ := BenchmarkBoundedGraphNull.exists_borel_reduction
    graph ballSize ball measurable_ball ball_complete cantorCode measurable_cantorCode cantorCode_injective
  exact ⟨F, hF, hb, fun x y => (orbit_iff_reachable x y).trans (hr x y)⟩

theorem exists_borel_product_shift_null_reduction :
    ∃ F : (ℕ → Point) → (ℕ → ℝ), Measurable F ∧ (∀ x j, 0 ≤ F x j ∧ F x j ≤ 1) ∧
      ∀ x y, (∀ i, Orbit (x i) (y i)) ↔ Tendsto (fun j => F x j - F y j) atTop (𝓝 0) := by
  obtain ⟨F, hF, hb, hr⟩ := exists_borel_shift_null_reduction
  exact BenchmarkBoundedNullProduct.exists_product_reduction Orbit F hF hb hr

end BenchmarkShift
end
end Source8
end BenchmarkCountableProof

/- Whole source module: CountablePositiveMission -/
namespace BenchmarkCountableProof
section Source9
/-! Exact Prove2Me mission interfaces for the positive part of Theorem 1.1.
The nonreductions against finite ℓp are separate statements. -/

namespace BenchmarkCountablePositive

theorem eInfinity_reduces_null :
    BenchmarkComparisons.BorelReduces BenchmarkComparisons.EInfinity
      BenchmarkComparisons.NullDifference := by
  obtain ⟨F, hF, _hb, hr⟩ := BenchmarkShift.exists_borel_shift_null_reduction
  exact ⟨F, hF, hr⟩

theorem product_eInfinity_reduces_null :
    BenchmarkComparisons.BorelReduces
      (BenchmarkComparisons.ProductRelation BenchmarkComparisons.EInfinity)
      BenchmarkComparisons.NullDifference := by
  obtain ⟨F, hF, _hb, hr⟩ := BenchmarkShift.exists_borel_product_shift_null_reduction
  exact ⟨F, hF, hr⟩

end BenchmarkCountablePositive
end Source9
end BenchmarkCountableProof

/- Whole source module: ShiftBernoulliMeasure -/
namespace BenchmarkCountableProof
section Source10
/-! The actual fair Bernoulli probability on the full free-group shift.
All singletons and all shift orbits are null, and shifts preserve it. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

noncomputable section

namespace BenchmarkShift

def fairLaw : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance fairLaw_probability : IsProbabilityMeasure fairLaw := by
  constructor
  norm_num [fairLaw, ENNReal.inv_two_add_inv_two]

lemma fairLaw_singleton (b : Bool) : fairLaw {b} = (1 / 2 : ℝ≥0∞) := by
  cases b <;> norm_num [fairLaw, Measure.dirac_apply]

def bernoulli : Measure Point := Measure.infinitePi (fun _ : Group => fairLaw)

instance bernoulli_probability : IsProbabilityMeasure bernoulli := by
  unfold bernoulli
  infer_instance

def natGroupEmbedding : ℕ ↪ Group where
  toFun n := FreeGroup.map (fun _ : Unit => (0 : Fin 2))
    (FreeGroup.freeGroupUnitEquivInt.symm (n : ℤ))
  inj' := (FreeGroup.map_injective (f := fun _ : Unit => (0 : Fin 2))
    (fun _ _ _ => Subsingleton.elim _ _)).comp
      (FreeGroup.freeGroupUnitEquivInt.symm.injective.comp Int.ofNat_injective)

lemma bernoulli_singleton_bound (x : Point) (n : ℕ) :
    bernoulli {x} ≤ (1 / 2 : ℝ≥0∞) ^ n := by
  classical
  let s : Finset Group := (Finset.range n).image natGroupEmbedding
  have hs : s.card = n := by
    rw [Finset.card_image_of_injective _ natGroupEmbedding.injective, Finset.card_range]
  have hsub : ({x} : Set Point) ⊆ Set.pi (s : Set Group) (fun g => {x g}) := by
    intro y hy
    subst y
    simp
  calc
    bernoulli {x} ≤ bernoulli (Set.pi (s : Set Group) (fun g => {x g})) := measure_mono hsub
    _ = ∏ g ∈ s, fairLaw {x g} := Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)
    _ = (1 / 2 : ℝ≥0∞) ^ n := by simp only [fairLaw_singleton, Finset.prod_const, hs]

theorem bernoulli_singleton_zero (x : Point) : bernoulli {x} = 0 := by
  have hr : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ≥0∞) ^ n) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_zero, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using ENNReal.tendsto_ofReal hr
  exact le_antisymm (ge_of_tendsto hlim (Eventually.of_forall (bernoulli_singleton_bound x))) bot_le

instance bernoulli_noAtoms : NoAtoms bernoulli := ⟨bernoulli_singleton_zero⟩

theorem orbit_countable (x : Point) : {y | Orbit x y}.Countable := by
  have heq : {y | Orbit x y} = Set.range (fun g : Group => shift g x) := by
    ext y
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, (funext hg).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, fun _ => rfl⟩
  rw [heq]
  exact Set.countable_range _

theorem bernoulli_orbit_zero (x : Point) : bernoulli {y | Orbit x y} = 0 :=
  (orbit_countable x).measure_zero bernoulli

theorem measurePreserving_shift (g : Group) : MeasurePreserving (shift g) bernoulli bernoulli := by
  refine ⟨(continuous_shift g).measurable, ?_⟩
  have hmap := Measure.infinitePi_map_piCongrLeft (fun _ : Group => fairLaw) (Equiv.mulLeft g)
  have hfun : shift g = (MeasurableEquiv.piCongrLeft (fun _ : Group => Bool) (Equiv.mulLeft g)) := by
    funext x h
    obtain ⟨k, rfl⟩ := (Equiv.mulLeft g).surjective h
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    simp [shift]
  simpa only [← hfun, bernoulli] using hmap

end BenchmarkShift
end
end Source10
end BenchmarkCountableProof

/- Whole source module: ShiftWalshCharacters -/
namespace BenchmarkCountableProof
section Source11
/-! Walsh characters on the actual fair free-group Bernoulli shift. These
are the concrete orthogonal coordinates for the remaining spectral-gap
argument. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators symmDiff

noncomputable section

namespace BenchmarkShift

local instance : DecidableEq Group := Classical.decEq Group

def coinSign (b : Bool) : ℝ := if b then 1 else -1

lemma abs_coinSign (b : Bool) : |coinSign b| = 1 := by cases b <;> norm_num [coinSign]
lemma coinSign_sq (b : Bool) : coinSign b ^ 2 = 1 := by cases b <;> norm_num [coinSign]

theorem continuous_coinSign : Continuous coinSign := continuous_of_discreteTopology

lemma integrable_coinSign : Integrable coinSign fairLaw :=
  Integrable.of_bound continuous_coinSign.measurable.aestronglyMeasurable 1
    (ae_of_all _ (fun b => by simp only [Real.norm_eq_abs, abs_coinSign, le_refl]))

lemma integral_coinSign : (∫ b, coinSign b ∂fairLaw) = 0 := by
  rw [integral_fintype integrable_coinSign]
  norm_num [Measure.real, fairLaw_singleton, coinSign]

def walsh (S : Finset Group) (x : Point) : ℝ := ∏ g ∈ S, coinSign (x g)

theorem continuous_walsh (S : Finset Group) : Continuous (walsh S) := by
  exact continuous_finsetProd S (fun g _ => continuous_coinSign.comp (continuous_apply g))

lemma abs_walsh (S : Finset Group) (x : Point) : |walsh S x| = 1 := by
  unfold walsh
  rw [Finset.abs_prod]
  simp only [abs_coinSign, Finset.prod_const_one]

lemma walsh_sq (S : Finset Group) (x : Point) : walsh S x ^ 2 = 1 := by
  unfold walsh
  rw [← Finset.prod_pow]
  simp only [coinSign_sq, Finset.prod_const_one]

lemma memLp_walsh (S : Finset Group) (p : ℝ≥0∞) : MemLp (walsh S) p bernoulli :=
  MemLp.of_bound (continuous_walsh S).measurable.aestronglyMeasurable 1
    (ae_of_all _ (fun x => by simp only [Real.norm_eq_abs, abs_walsh, le_refl]))

lemma integral_walsh (S : Finset Group) : (∫ x, walsh S x ∂bernoulli) = if S = ∅ then 1 else 0 := by
  classical
  let f : (S → Bool) → ℝ := fun x => ∏ g : S, coinSign (x g)
  have hrep : walsh S = fun x => f (S.restrict x) := by
    funext x
    dsimp [walsh, f]
    exact (Finset.prod_attach S (fun g => coinSign (x g))).symm
  rw [hrep]
  have hf : AEStronglyMeasurable f (Measure.pi (fun _ : S => fairLaw)) :=
    (measurable_of_countable f).aestronglyMeasurable
  rw [show bernoulli = Measure.infinitePi (fun _ : Group => fairLaw) from rfl,
    integral_restrict_infinitePi (fun _ : Group => fairLaw) hf,
    integral_fintype_prod_eq_prod (fun _ : S => coinSign)]
  simp only [integral_coinSign]
  by_cases hS : S = ∅
  · subst S
    simp
  · rw [if_neg hS]
    obtain ⟨g, hg⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    exact Finset.prod_eq_zero (Finset.mem_univ ⟨g, hg⟩) rfl

lemma walsh_mul (S T : Finset Group) (x : Point) :
    walsh S x * walsh T x = walsh (S ∆ T) x := by
  classical
  have hu : S ∪ T = (S ∆ T) ∪ (S ∩ T) := by
    ext g
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_symmDiff]
    tauto
  have hd : Disjoint (S ∆ T) (S ∩ T) := by
    rw [Finset.disjoint_left]
    intro g hg hboth
    simp only [Finset.mem_symmDiff, Finset.mem_inter] at hg hboth
    tauto
  have hprod : walsh (S ∪ T) x = walsh (S ∆ T) x * walsh (S ∩ T) x := by
    unfold walsh
    rw [hu, Finset.prod_union hd]
  calc
    walsh S x * walsh T x = walsh (S ∪ T) x * walsh (S ∩ T) x :=
      (Finset.prod_union_inter (f := fun g => coinSign (x g))).symm
    _ = (walsh (S ∆ T) x * walsh (S ∩ T) x) * walsh (S ∩ T) x := by rw [hprod]
    _ = walsh (S ∆ T) x := by rw [mul_assoc, ← sq, walsh_sq, mul_one]

theorem integral_walsh_mul (S T : Finset Group) :
    (∫ x, walsh S x * walsh T x ∂bernoulli) = if S = T then 1 else 0 := by
  simp_rw [walsh_mul]
  rw [integral_walsh]
  simp only [Finset.symmDiff_eq_empty]

end BenchmarkShift
end
end Source11
end BenchmarkCountableProof

/- Whole source module: WalshContinuousDensity -/
namespace BenchmarkCountableProof
section Source12
/-! Finite linear combinations of Walsh characters are uniformly dense in
the continuous real-valued functions on the full binary shift. -/

open Set
open scoped Topology symmDiff

noncomputable section

namespace BenchmarkShift

local instance : DecidableEq Group := Classical.decEq Group

def continuousWalsh (S : Finset Group) : C(Point, ℝ) := ⟨walsh S, continuous_walsh S⟩

lemma continuousWalsh_empty : continuousWalsh ∅ = 1 := by ext x; simp [continuousWalsh, walsh]

lemma continuousWalsh_mul (S T : Finset Group) :
    continuousWalsh S * continuousWalsh T = continuousWalsh (S ∆ T) := by
  ext x
  exact walsh_mul S T x

def walshSubmonoid : Submonoid C(Point, ℝ) where
  carrier := Set.range continuousWalsh
  one_mem' := ⟨∅, continuousWalsh_empty⟩
  mul_mem' := by
    rintro a b ⟨S, rfl⟩ ⟨T, rfl⟩
    exact ⟨S ∆ T, (continuousWalsh_mul S T).symm⟩

def walshAlgebra : Subalgebra ℝ C(Point, ℝ) := Algebra.adjoin ℝ (Set.range continuousWalsh)

lemma walshAlgebra_toSubmodule : walshAlgebra.toSubmodule =
    Submodule.span ℝ (Set.range continuousWalsh) := by
  unfold walshAlgebra
  rw [Algebra.adjoin_eq_span]
  change Submodule.span ℝ (Submonoid.closure (walshSubmonoid : Set C(Point, ℝ)) : Set C(Point, ℝ)) = _
  rw [walshSubmonoid.closure_eq]
  rfl

lemma coinSign_injective : Function.Injective coinSign := by
  intro a b h
  cases a <;> cases b <;> first | rfl | norm_num [coinSign] at h

lemma walshAlgebra_separatesPoints : walshAlgebra.SeparatesPoints := by
  intro x y hxy
  have hex : ∃ g : Group, x g ≠ y g := by
    by_contra h
    push Not at h
    exact hxy (funext h)
  obtain ⟨g, hg⟩ := hex
  refine ⟨walsh {g}, ⟨continuousWalsh {g}, Algebra.subset_adjoin ⟨{g}, rfl⟩, rfl⟩, ?_⟩
  intro heq
  apply hg
  apply coinSign_injective
  simpa only [walsh, Finset.prod_singleton] using heq

theorem dense_continuous_walsh_span :
    Dense (Submodule.span ℝ (Set.range continuousWalsh) : Set C(Point, ℝ)) := by
  have hclosure := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    walshAlgebra walshAlgebra_separatesPoints
  have hdense : Dense (walshAlgebra : Set C(Point, ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, hclosure]
    rfl
  have hset : (walshAlgebra : Set C(Point, ℝ)) =
      (Submodule.span ℝ (Set.range continuousWalsh) : Set C(Point, ℝ)) := by
    rw [← walshAlgebra_toSubmodule]
    rfl
  rwa [← hset]

end BenchmarkShift
end
end Source12
end BenchmarkCountableProof

/- Whole source module: WalshL2Basis -/
namespace BenchmarkCountableProof
section Source13
/-! A complete Walsh Hilbert basis for the actual Bernoulli L² space.
Uniform Stone-Weierstrass density is transported through the continuous
map from continuous functions to L². -/

open MeasureTheory Filter Set
open scoped Topology ENNReal InnerProductSpace

noncomputable section

namespace BenchmarkShift

local instance : DecidableEq Group := Classical.decEq Group

abbrev BernoulliL2 := Lp ℝ 2 bernoulli

def walshL2 (S : Finset Group) : BernoulliL2 :=
  ContinuousMap.toLp 2 bernoulli ℝ (continuousWalsh S)

lemma walshL2_ae (S : Finset Group) : (walshL2 S : Point → ℝ) =ᵐ[bernoulli] walsh S :=
  ContinuousMap.coeFn_toLp (p := 2) (μ := bernoulli) (𝕜 := ℝ) (continuousWalsh S)

theorem inner_walshL2 (S T : Finset Group) :
    ⟪walshL2 S, walshL2 T⟫_ℝ = if S = T then 1 else 0 := by
  rw [L2.inner_def]
  apply Eq.trans _ (integral_walsh_mul S T)
  apply integral_congr_ae
  filter_upwards [walshL2_ae S, walshL2_ae T] with x hx hy
  rw [hx, hy, Real.inner_apply]

theorem orthonormal_walshL2 : Orthonormal ℝ walshL2 :=
  orthonormal_iff_ite.mpr inner_walshL2

theorem dense_walshL2_span : Dense (Submodule.span ℝ (Set.range walshL2) : Set BernoulliL2) := by
  let T : C(Point, ℝ) →L[ℝ] BernoulliL2 := ContinuousMap.toLp 2 bernoulli ℝ
  have hT : DenseRange T := ContinuousMap.toLp_denseRange
    (E := ℝ) (μ := bernoulli) (p := 2) (𝕜 := ℝ) (by norm_num)
  have hd := hT.dense_image T.continuous dense_continuous_walsh_span
  have himage : T '' (Submodule.span ℝ (Set.range continuousWalsh) : Set C(Point, ℝ)) =
      ((Submodule.span ℝ (Set.range continuousWalsh)).map T.toLinearMap : Set BernoulliL2) := rfl
  rw [himage, Submodule.map_span, ← Set.range_comp] at hd
  exact hd

def walshBasis : HilbertBasis (Finset Group) ℝ BernoulliL2 :=
  HilbertBasis.mk orthonormal_walshL2 (by
    rw [(Submodule.dense_iff_topologicalClosure_eq_top).mp dense_walshL2_span])

@[simp] lemma walshBasis_apply (S : Finset Group) : walshBasis S = walshL2 S := by
  simp [walshBasis]

end BenchmarkShift
end
end Source13
end BenchmarkCountableProof

/- Whole source module: FiniteSupportTranslation -/
namespace BenchmarkCountableProof
section Source14
/-! Translation acts freely on nonempty finite subsets of a torsion-free
group. This is the stabilizer fact needed for the Walsh decomposition of
the free-group Bernoulli representation. -/

noncomputable section

namespace BenchmarkFiniteSupport

theorem translate_eq_self_implies_one
    {G : Type*} [Group G] [DecidableEq G] [IsMulTorsionFree G]
    (S : Finset G) (hS : S.Nonempty) (g : G)
    (htranslate : S.image (fun a => g * a) = S) : g = 1 := by
  classical
  obtain ⟨a, ha⟩ := hS
  have hstep : ∀ b ∈ S, g * b ∈ S := by
    intro b hb
    rw [← htranslate]
    exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hmem : ∀ n : ℕ, g ^ n * a ∈ S := by
    intro n
    induction n with
    | zero => simpa using ha
    | succ n ih => simpa only [pow_succ', mul_assoc] using hstep (g ^ n * a) ih
  let f : ℕ → S := fun n => ⟨g ^ n * a, hmem n⟩
  have hninj : ¬ Function.Injective f := not_injective_infinite_finite f
  simp only [Function.Injective, not_forall, _root_.not_imp] at hninj
  obtain ⟨n, m, heq, hne⟩ := hninj
  have hp : g ^ n = g ^ m := mul_right_cancel (congrArg Subtype.val heq)
  rcases lt_or_gt_of_ne hne with hnm | hmn
  · have hz : g ^ (m - n) = 1 := by rw [pow_sub g hnm.le, ← hp, mul_inv_cancel]
    exact (pow_eq_one_iff_left (by omega : m - n ≠ 0)).mp hz
  · have hz : g ^ (n - m) = 1 := by rw [pow_sub g hmn.le, hp, mul_inv_cancel]
    exact (pow_eq_one_iff_left (by omega : n - m ≠ 0)).mp hz

theorem freeGroup_translate_eq_self_implies_one
    (S : Finset BenchmarkShift.Group) (hS : S.Nonempty) (g : BenchmarkShift.Group)
    (htranslate : S.image (fun a => g * a) = S) : g = 1 :=
  translate_eq_self_implies_one S hS g htranslate

end BenchmarkFiniteSupport
end
end Source14
end BenchmarkCountableProof

/- Whole source module: WalshShiftAction -/
namespace BenchmarkCountableProof
section Source15
/-! The actual Koopman shifts permute the Walsh basis by left translation
of its finite supports. The empty coefficient is the integral. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal InnerProductSpace

noncomputable section

namespace BenchmarkShift

def supportTranslate (g : Group) (S : Finset Group) : Finset Group :=
  S.image (fun h => g * h)

lemma walsh_shift_inverse (g : Group) (S : Finset Group) (x : Point) :
    walsh S (shift g⁻¹ x) = walsh (supportTranslate g S) x := by
  classical
  unfold walsh supportTranslate
  rw [Finset.prod_image]
  · simp only [shift, inv_inv]
  · intro a _ b _ hab
    exact mul_left_cancel hab

def koopman (g : Group) : BernoulliL2 →ₗᵢ[ℝ] BernoulliL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ (shift g⁻¹) (measurePreserving_shift g⁻¹)

theorem koopman_walshL2 (g : Group) (S : Finset Group) :
    koopman g (walshL2 S) = walshL2 (supportTranslate g S) := by
  apply Lp.ext
  have hcomp := Lp.coeFn_compMeasurePreserving (walshL2 S) (measurePreserving_shift g⁻¹)
  have hsource := (measurePreserving_shift g⁻¹).quasiMeasurePreserving.ae (walshL2_ae S)
  filter_upwards [hcomp, hsource, walshL2_ae (supportTranslate g S)] with x hc hs ht
  change (Lp.compMeasurePreserving (shift g⁻¹) (measurePreserving_shift g⁻¹) (walshL2 S)) x = _
  rw [hc, Function.comp_apply, hs, ht]
  exact walsh_shift_inverse g S x

theorem koopman_walshBasis (g : Group) (S : Finset Group) :
    koopman g (walshBasis S) = walshBasis (supportTranslate g S) := by
  simpa only [walshBasis_apply] using koopman_walshL2 g S

theorem supportTranslate_faithful (S : Finset Group) (hS : S.Nonempty)
    (g : Group) (h : supportTranslate g S = S) : g = 1 :=
  BenchmarkFiniteSupport.freeGroup_translate_eq_self_implies_one S hS g h

theorem empty_walsh_coefficient (u : BernoulliL2) :
    walshBasis.repr u ∅ = ∫ x, u x ∂bernoulli := by
  rw [HilbertBasis.repr_apply_apply, walshBasis_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [walshL2_ae ∅] with x hx
  rw [hx, Real.inner_apply]
  simp [walsh]

end BenchmarkShift
end
end Source15
end BenchmarkCountableProof

/- Whole source module: WalshSupportOrbits -/
namespace BenchmarkCountableProof
section Source16
/-! Nonconstant Walsh supports form a disjoint union of free regular
orbits. The displayed inverse coordinate map sends `(q,g)` to `g • q.out`. -/

noncomputable section

namespace BenchmarkShift

abbrev NonemptySupport := {S : Finset Group // S.Nonempty}

instance supportMulAction : MulAction Group NonemptySupport where
  smul g S := ⟨supportTranslate g S, S.property.image _⟩
  one_smul := by
    intro S
    apply Subtype.ext
    change supportTranslate 1 S.val = S.val
    ext a
    simp only [supportTranslate, Finset.mem_image, one_mul]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  mul_smul := by
    intro g h S
    apply Subtype.ext
    change supportTranslate (g * h) S.val = supportTranslate g (supportTranslate h S.val)
    simp only [supportTranslate, Finset.image_image, Function.comp_def, mul_assoc]

lemma support_smul_faithful (g : Group) (S : NonemptySupport) (h : g • S = S) : g = 1 :=
  supportTranslate_faithful S S.property g (congrArg Subtype.val h)

lemma support_right_cancel (g h : Group) (S : NonemptySupport) (heq : g • S = h • S) : g = h := by
  have hfix : (h⁻¹ * g) • S = S := by rw [mul_smul, heq, inv_smul_smul]
  have hh := support_smul_faithful (h⁻¹ * g) S hfix
  exact (inv_mul_eq_one.mp hh).symm

abbrev SupportOrbit := Quotient (MulAction.orbitRel Group NonemptySupport)

local instance : Setoid NonemptySupport := MulAction.orbitRel Group NonemptySupport

def regularOrbitMap (p : SupportOrbit × Group) : NonemptySupport := p.2 • p.1.out

lemma support_class_smul (g : Group) (S : NonemptySupport) :
    (Quotient.mk' (g • S) : SupportOrbit) = Quotient.mk' S := by
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  exact ⟨g, rfl⟩

theorem regularOrbitMap_bijective : Function.Bijective regularOrbitMap := by
  constructor
  · rintro ⟨q, g⟩ ⟨r, h⟩ heq
    have hclass := congrArg (fun S => (Quotient.mk' S : SupportOrbit)) heq
    have hqr : q = r := by
      have hclass' : (Quotient.mk' q.out : SupportOrbit) = Quotient.mk' r.out := by
        simpa only [regularOrbitMap, support_class_smul] using hclass
      have hq : (Quotient.mk' q.out : SupportOrbit) = q := Quotient.out_eq q
      have hr : (Quotient.mk' r.out : SupportOrbit) = r := Quotient.out_eq r
      exact hq.symm.trans (hclass'.trans hr)
    subst r
    have hgh : g = h := support_right_cancel g h q.out heq
    exact Prod.ext rfl hgh
  · intro S
    let q : SupportOrbit := Quotient.mk' S
    have hq : (Quotient.mk' q.out : SupportOrbit) = Quotient.mk' S := Quotient.out_eq q
    have hr := MulAction.orbitRel_apply.mp (Quotient.exact hq.symm)
    obtain ⟨g, hg⟩ := hr
    exact ⟨(q, g), hg⟩

def supportOrbitEquiv : NonemptySupport ≃ SupportOrbit × Group :=
  (Equiv.ofBijective regularOrbitMap regularOrbitMap_bijective).symm

@[simp] lemma supportOrbitEquiv_symm_apply (q : SupportOrbit) (g : Group) :
    supportOrbitEquiv.symm (q, g) = g • q.out := rfl

theorem supportOrbitEquiv_symm_mul (q : SupportOrbit) (g h : Group) :
    supportOrbitEquiv.symm (q, g * h) = g • supportOrbitEquiv.symm (q, h) := by
  simp only [supportOrbitEquiv_symm_apply, mul_smul]

end BenchmarkShift
end
end Source16
end BenchmarkCountableProof

/- Whole source module: WalshKoopmanRepresentation -/
namespace BenchmarkCountableProof
section Source17
/-! Group laws and coefficient transport for the actual Koopman action. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal InnerProductSpace

noncomputable section

namespace BenchmarkShift

lemma koopman_ae (g : Group) (u : BernoulliL2) :
    (koopman g u : Point → ℝ) =ᵐ[bernoulli] fun x => u (shift g⁻¹ x) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_shift g⁻¹)

theorem koopman_one (u : BernoulliL2) : koopman 1 u = u := by
  apply Lp.ext
  filter_upwards [koopman_ae 1 u] with x hx
  simpa only [inv_one, shift_one] using hx

theorem koopman_mul (g h : Group) (u : BernoulliL2) : koopman g (koopman h u) = koopman (g * h) u := by
  apply Lp.ext
  have hg := koopman_ae g (koopman h u)
  have hh := (measurePreserving_shift g⁻¹).quasiMeasurePreserving.ae
    (koopman_ae h u)
  have hgh := koopman_ae (g * h) u
  filter_upwards [hg, hh, hgh] with x hx hy hz
  calc
    koopman g (koopman h u) x = koopman h u (shift g⁻¹ x) := hx
    _ = u (shift h⁻¹ (shift g⁻¹ x)) := hy
    _ = u (shift (g * h)⁻¹ x) := by rw [shift_mul, mul_inv_rev]
    _ = koopman (g * h) u x := hz.symm

theorem inner_walshL2_koopman (g : Group) (S : Finset Group) (u : BernoulliL2) :
    ⟪walshL2 S, koopman g u⟫_ℝ = ⟪walshL2 (supportTranslate g⁻¹ S), u⟫_ℝ := by
  have h := (koopman g).inner_map_map (koopman g⁻¹ (walshL2 S)) u
  rw [koopman_mul, mul_inv_cancel, koopman_one, koopman_walshL2] at h
  exact h

theorem walsh_coefficient_koopman (g : Group) (S : Finset Group) (u : BernoulliL2) :
    walshBasis.repr (koopman g u) S = walshBasis.repr u (supportTranslate g⁻¹ S) := by
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, walshBasis_apply, walshBasis_apply]
  exact inner_walshL2_koopman g S u

end BenchmarkShift
end
end Source17
end BenchmarkCountableProof

/- Whole source module: L2CoordinateProjection -/
namespace BenchmarkCountableProof
section Source18
/-! Coordinate projections and permutation isometries on actual real ℓ².
These are the projection-mass interfaces for the free-group cone argument. -/

open Set
open scoped ENNReal InnerProductSpace

noncomputable section

namespace BenchmarkCoordinateProjection

variable {I : Type*}
abbrev Space (I : Type*) := lp (fun _ : I => ℝ) 2

local instance (s : Set I) : DecidablePred s := Classical.decPred s

def project (s : Set I) (v : Space I) : Space I :=
  ⟨fun i => if i ∈ s then v i else 0, (lp.memℓp v).mono' (fun i => by
    by_cases hi : i ∈ s <;> simp [hi])⟩

lemma project_apply (s : Set I) (v : Space I) (i : I) :
    project s v i = if i ∈ s then v i else 0 := rfl

theorem norm_project_le (s : Set I) (v : Space I) : ‖project s v‖ ≤ ‖v‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro i
  by_cases hi : i ∈ s <;> simp [project_apply, hi]

def projectLinear (s : Set I) : Space I →ₗ[ℝ] Space I where
  toFun := project s
  map_add' v w := by
    ext i
    change (if i ∈ s then v i + w i else 0) =
      (if i ∈ s then v i else 0) + (if i ∈ s then w i else 0)
    by_cases hi : i ∈ s <;> simp [hi]
  map_smul' r v := by
    ext i
    by_cases hi : i ∈ s <;> simp [project_apply, hi]

def projection (s : Set I) : Space I →L[ℝ] Space I :=
  (projectLinear s).mkContinuous 1 (fun v => by simpa only [one_mul] using norm_project_le s v)

@[simp] lemma projection_apply (s : Set I) (v : Space I) : projection s v = project s v := rfl

theorem project_add_compl (s : Set I) (v : Space I) : project s v + project sᶜ v = v := by
  ext i
  change project s v i + project sᶜ v i = v i
  rw [project_apply, project_apply]
  by_cases hi : i ∈ s <;> simp [hi]

theorem inner_project_disjoint (s t : Set I) (hdis : Disjoint s t) (v : Space I) :
    ⟪project s v, project t v⟫_ℝ = 0 := by
  rw [lp.inner_eq_tsum]
  have hz : ∀ i, ⟪project s v i, project t v i⟫_ℝ = 0 := by
    intro i
    by_cases hs : i ∈ s
    · have ht : i ∉ t := fun ht => Set.disjoint_left.mp hdis hs ht
      simp [project_apply, hs, ht, Real.inner_apply]
    · simp [project_apply, hs, Real.inner_apply]
  simp_rw [hz]
  simp

theorem norm_sq_project_add_compl (s : Set I) (v : Space I) :
    ‖project s v‖ ^ 2 + ‖project sᶜ v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h := norm_add_sq_real (project s v) (project sᶜ v)
  rw [project_add_compl, inner_project_disjoint s sᶜ disjoint_compl_right] at h
  linarith

theorem project_union (s t : Set I) (hdis : Disjoint s t) (v : Space I) :
    project (s ∪ t) v = project s v + project t v := by
  ext i
  change project (s ∪ t) v i = project s v i + project t v i
  rw [project_apply, project_apply, project_apply]
  by_cases hs : i ∈ s
  · have ht : i ∉ t := fun ht => Set.disjoint_left.mp hdis hs ht
    simp [hs, ht]
  · by_cases ht : i ∈ t <;> simp [hs, ht]

theorem norm_sq_project_union (s t : Set I) (hdis : Disjoint s t) (v : Space I) :
    ‖project (s ∪ t) v‖ ^ 2 = ‖project s v‖ ^ 2 + ‖project t v‖ ^ 2 := by
  rw [project_union s t hdis, norm_add_sq_real, inner_project_disjoint s t hdis]
  ring

theorem four_projection_mass_le (s₁ s₂ s₃ s₄ : Set I)
    (h12 : Disjoint s₁ s₂) (h13 : Disjoint s₁ s₃) (h14 : Disjoint s₁ s₄)
    (h23 : Disjoint s₂ s₃) (h24 : Disjoint s₂ s₄) (h34 : Disjoint s₃ s₄)
    (v : Space I) :
    ‖project s₁ v‖ ^ 2 + ‖project s₂ v‖ ^ 2 + ‖project s₃ v‖ ^ 2 + ‖project s₄ v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have hu : Disjoint (s₁ ∪ s₂) (s₃ ∪ s₄) := by
    rw [Set.disjoint_left]
    intro i hi hj
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact Set.disjoint_left.mp h13 hi hj
    · exact Set.disjoint_left.mp h14 hi hj
    · exact Set.disjoint_left.mp h23 hi hj
    · exact Set.disjoint_left.mp h24 hi hj
  have hsum := norm_sq_project_union (s₁ ∪ s₂) (s₃ ∪ s₄) hu v
  rw [norm_sq_project_union s₁ s₂ h12, norm_sq_project_union s₃ s₄ h34] at hsum
  have hb := norm_project_le ((s₁ ∪ s₂) ∪ (s₃ ∪ s₄)) v
  nlinarith [norm_nonneg (project ((s₁ ∪ s₂) ∪ (s₃ ∪ s₄)) v), norm_nonneg v]

def permute (e : I ≃ I) (v : Space I) : Space I :=
  ⟨fun i => v (e.symm i), (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    (((lp.memℓp v).summable (by norm_num)).comp_injective e.symm.injective)⟩

@[simp] lemma permute_apply (e : I ≃ I) (v : Space I) (i : I) : permute e v i = v (e.symm i) := rfl

theorem norm_permute (e : I ≃ I) (v : Space I) : ‖permute e v‖ = ‖v‖ := by
  have heq : (∑' i, ‖permute e v i‖ ^ (2 : ℝ≥0∞).toReal) =
      ∑' i, ‖v i‖ ^ (2 : ℝ≥0∞).toReal := by
    change (∑' i, ‖v (e.symm i)‖ ^ (2 : ℝ≥0∞).toReal) = _
    exact e.symm.tsum_eq (fun i => ‖v i‖ ^ (2 : ℝ≥0∞).toReal)
  rw [← lp.norm_rpow_eq_tsum (by norm_num), ← lp.norm_rpow_eq_tsum (by norm_num)] at heq
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at heq
  nlinarith [norm_nonneg (permute e v), norm_nonneg v]

def permutation (e : I ≃ I) : Space I →ₗᵢ[ℝ] Space I where
  toFun := permute e
  map_add' v w := by ext i; rfl
  map_smul' r v := by ext i; rfl
  norm_map' := norm_permute e

theorem project_permute (s : Set I) (e : I ≃ I) (v : Space I) :
    project s (permute e v) = permute e (project (e ⁻¹' s) v) := by
  ext i
  simp only [project_apply, permute_apply, Set.mem_preimage, Equiv.apply_symm_apply]

theorem norm_project_permute (s : Set I) (e : I ≃ I) (v : Space I) :
    ‖project s (permute e v)‖ = ‖project (e ⁻¹' s) v‖ := by
  rw [project_permute, norm_permute]

theorem norm_project_permute_pair (s t : Set I) (e : I ≃ I)
    (hpre : e ⁻¹' s = tᶜ) (v : Space I) :
    ‖project s (permute e v)‖ ^ 2 + ‖project t v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [norm_project_permute, hpre]
  simpa only [add_comm] using norm_sq_project_add_compl t v

end BenchmarkCoordinateProjection
end
end Source18
end BenchmarkCountableProof

/- Whole source module: FreeGroupCones -/
namespace BenchmarkCountableProof
section Source19
/-! First-letter cone cancellation for the free group on two generators.
Left multiplication by a letter sends the complement of its inverse
cone bijectively onto its own cone. -/

open Set

noncomputable section

namespace BenchmarkShift

def cone (a : Letter) : Set Group := {g | g.toWord.head? = some a}

lemma letterGroup_eq_mk (a : Letter) : letterGroup a = FreeGroup.mk [a] := by
  rcases a with ⟨i, b⟩
  cases b <;> simp [letterGroup, FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]

lemma toWord_letter_mul (a : Letter) (g : Group) :
    (letterGroup a * g).toWord = FreeGroup.reduce (a :: g.toWord) := by
  rw [letterGroup_eq_mk, ← FreeGroup.mk_toWord (x := g), FreeGroup.mul_mk, FreeGroup.toWord_mk]
  simp only [List.singleton_append, FreeGroup.toWord_mk, FreeGroup.reduce_toWord]

lemma cancellation_iff_reverse (a b : Letter) :
    (a.1 = b.1 ∧ a.2 = !b.2) ↔ b = reverseLetter a := by
  rcases a with ⟨i, ab⟩
  rcases b with ⟨j, bb⟩
  cases ab <;> cases bb <;> simp [reverseLetter, Prod.ext_iff, eq_comm]

lemma not_reduced_reverse_cons (a : Letter) (L : List Letter) :
    ¬ FreeGroup.IsReduced (reverseLetter a :: a :: L) := by
  rcases a with ⟨i, b⟩
  cases b <;> simp [reverseLetter, FreeGroup.isReduced_cons_cons]

theorem cone_letter_mul_iff (a : Letter) (g : Group) :
    letterGroup a * g ∈ cone a ↔ g ∉ cone (reverseLetter a) := by
  unfold cone
  simp only [mem_setOf_eq]
  rw [toWord_letter_mul, FreeGroup.reduce.cons, FreeGroup.reduce_toWord]
  cases hw : g.toWord with
  | nil => simp
  | cons b L =>
      change (if a.1 = b.1 ∧ a.2 = !b.2 then L else a :: b :: L).head? = some a ↔
        (some b : Option Letter) ≠ some (reverseLetter a)
      by_cases hb : b = reverseLetter a
      · rw [if_pos ((cancellation_iff_reverse a b).mpr hb)]
        simp only [hb, ne_eq, not_true_eq_false, iff_false]
        intro hhead
        have hred : FreeGroup.IsReduced (b :: L) := by
          rw [← hw]
          exact FreeGroup.isReduced_toWord
        cases L with
        | nil => simp at hhead
        | cons c tail =>
            have hca : c = a := Option.some.inj hhead
            subst c
            rw [hb] at hred
            exact not_reduced_reverse_cons a tail hred
      · have hc : ¬ (a.1 = b.1 ∧ a.2 = !b.2) :=
          fun h => hb ((cancellation_iff_reverse a b).mp h)
        simp only [if_neg hc, List.head?_cons, true_iff, ne_eq, Option.some.injEq]
        exact hb

theorem cone_preimage_left (a : Letter) :
    (fun g : Group => letterGroup a * g) ⁻¹' cone a = (cone (reverseLetter a))ᶜ := by
  ext g
  exact cone_letter_mul_iff a g

theorem cone_disjoint {a b : Letter} (hab : a ≠ b) : Disjoint (cone a) (cone b) := by
  rw [Set.disjoint_left]
  intro g ha hb
  exact hab (Option.some.inj (ha.symm.trans hb))

end BenchmarkShift
end
end Source19
end BenchmarkCountableProof

/- Whole source module: ProjectionMassGap -/
namespace BenchmarkCountableProof
section Source20
noncomputable section

namespace BenchmarkProjectionGap

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem projection_mass_variation (P : H →L[ℝ] H)
    (hP : ∀ w, ‖P w‖ ≤ ‖w‖) (u v : H) (huv : ‖u‖ = ‖v‖) :
    ‖P u‖ ^ 2 - ‖P v‖ ^ 2 ≤ 2 * ‖v‖ * ‖u - v‖ := by
  have hd : ‖P u‖ - ‖P v‖ ≤ ‖u - v‖ := by
    calc
      ‖P u‖ - ‖P v‖ ≤ ‖P u - P v‖ := norm_sub_norm_le _ _
      _ = ‖P (u - v)‖ := by rw [map_sub]
      _ ≤ ‖u - v‖ := hP _
  have hs : ‖P u‖ + ‖P v‖ ≤ 2 * ‖v‖ := by
    have h1 := hP u
    have h2 := hP v
    rw [huv] at h1
    linarith
  calc
    ‖P u‖ ^ 2 - ‖P v‖ ^ 2 = (‖P u‖ - ‖P v‖) * (‖P u‖ + ‖P v‖) := by ring
    _ ≤ ‖u - v‖ * (‖P u‖ + ‖P v‖) :=
      mul_le_mul_of_nonneg_right hd (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ ‖u - v‖ * (2 * ‖v‖) := mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ = 2 * ‖v‖ * ‖u - v‖ := by ring

theorem two_partition_gap (Pap Pam Pbp Pbm : H →L[ℝ] H)
    (hap : ∀ w, ‖Pap w‖ ≤ ‖w‖) (hbp : ∀ w, ‖Pbp w‖ ≤ ‖w‖)
    (v uA uB : H) (hA : ‖uA‖ = ‖v‖) (hB : ‖uB‖ = ‖v‖)
    (hpairA : ‖Pap uA‖ ^ 2 + ‖Pam v‖ ^ 2 = ‖v‖ ^ 2)
    (hpairB : ‖Pbp uB‖ ^ 2 + ‖Pbm v‖ ^ 2 = ‖v‖ ^ 2)
    (hmass : ‖Pap v‖ ^ 2 + ‖Pam v‖ ^ 2 + ‖Pbp v‖ ^ 2 + ‖Pbm v‖ ^ 2 ≤ ‖v‖ ^ 2) :
    ‖v‖ ^ 2 ≤ 8 * (‖uA - v‖ ^ 2 + ‖uB - v‖ ^ 2) := by
  have hvarA := projection_mass_variation Pap hap uA v hA
  have hvarB := projection_mass_variation Pbp hbp uB v hB
  have hnorm : ‖v‖ ^ 2 ≤ 2 * ‖v‖ * (‖uA - v‖ + ‖uB - v‖) := by
    nlinarith
  by_cases hz : ‖v‖ = 0
  · rw [hz]
    nlinarith [sq_nonneg ‖uA - v‖, sq_nonneg ‖uB - v‖]
  · have hv : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hlin : ‖v‖ ≤ 2 * (‖uA - v‖ + ‖uB - v‖) := by nlinarith
    have hs := sq_nonneg (‖uA - v‖ - ‖uB - v‖)
    have hproduct := mul_self_le_mul_self (norm_nonneg v) hlin
    nlinarith

end BenchmarkProjectionGap
end
end Source20
end BenchmarkCountableProof

/- Whole source module: RegularFreeGroupGap -/
namespace BenchmarkCountableProof
section Source21
/-! An actual uniform ℓ² spectral gap for arbitrary sums of the free
regular representation of F₂, obtained from its four first-letter cones. -/

open Set
open scoped ENNReal

noncomputable section

namespace BenchmarkRegularGap

open BenchmarkShift BenchmarkCoordinateProjection

variable {Q : Type*}

def coneSet (a : Letter) : Set (Q × Group) := {p | p.2 ∈ cone a}

def leftPermutation (a : Letter) : (Q × Group) ≃ (Q × Group) :=
  Equiv.prodCongr (Equiv.refl Q) (Equiv.mulLeft (letterGroup a))

lemma coneSet_preimage (a : Letter) :
    (leftPermutation (Q := Q) a) ⁻¹' coneSet a = (coneSet (reverseLetter a))ᶜ := by
  ext p
  exact cone_letter_mul_iff a p.2

lemma coneSet_disjoint {a b : Letter} (hab : a ≠ b) :
    Disjoint (coneSet (Q := Q) a) (coneSet b) := by
  rw [Set.disjoint_left]
  intro p ha hb
  exact Set.disjoint_left.mp (cone_disjoint hab) ha hb

theorem regular_free_group_gap (v : Space (Q × Group)) :
    ‖v‖ ^ 2 ≤ 8 *
      (‖permute (leftPermutation (0, true)) v - v‖ ^ 2 +
        ‖permute (leftPermutation (1, true)) v - v‖ ^ 2) := by
  let ap := coneSet (Q := Q) (0, true)
  let am := coneSet (Q := Q) (0, false)
  let bp := coneSet (Q := Q) (1, true)
  let bm := coneSet (Q := Q) (1, false)
  let eA := leftPermutation (Q := Q) (0, true)
  let eB := leftPermutation (Q := Q) (1, true)
  apply BenchmarkProjectionGap.two_partition_gap
    (projection ap) (projection am) (projection bp) (projection bm)
    (fun w => norm_project_le ap w) (fun w => norm_project_le bp w)
    v (permute eA v) (permute eB v) (norm_permute eA v) (norm_permute eB v)
  · exact norm_project_permute_pair ap am eA (coneSet_preimage (0, true)) v
  · exact norm_project_permute_pair bp bm eB (coneSet_preimage (1, true)) v
  · exact four_projection_mass_le ap am bp bm
      (coneSet_disjoint (by decide : ((0, true) : Letter) ≠ (0, false)))
      (coneSet_disjoint (by decide : ((0, true) : Letter) ≠ (1, true)))
      (coneSet_disjoint (by decide : ((0, true) : Letter) ≠ (1, false)))
      (coneSet_disjoint (by decide : ((0, false) : Letter) ≠ (1, true)))
      (coneSet_disjoint (by decide : ((0, false) : Letter) ≠ (1, false)))
      (coneSet_disjoint (by decide : ((1, true) : Letter) ≠ (1, false))) v

end BenchmarkRegularGap
end
end Source21
end BenchmarkCountableProof

/- Whole source module: BernoulliSpectralGap -/
namespace BenchmarkCountableProof
section Source22
/-! The actual fair F₂ Bernoulli shift has a quantitative L² spectral gap.
The proof reindexes the nonconstant Walsh coefficients into free regular
orbits, applies the first-letter cone estimate, and transports norms back. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal InnerProductSpace

noncomputable section

namespace BenchmarkShift

open BenchmarkCoordinateProjection BenchmarkRegularGap

def regularIndex (p : SupportOrbit × Group) : Finset Group := (supportOrbitEquiv.symm p).val

lemma regularIndex_injective : Function.Injective regularIndex :=
  Subtype.val_injective.comp supportOrbitEquiv.symm.injective

def regularCoefficients (u : BernoulliL2) : Space (SupportOrbit × Group) :=
  ⟨fun p => walshBasis.repr u (regularIndex p),
    (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
      (((lp.memℓp (walshBasis.repr u)).summable (by norm_num)).comp_injective regularIndex_injective)⟩

lemma coordinate_norm_sq {I : Type*} (v : Space I) : ‖v‖ ^ 2 = ∑' i, (v i) ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) v

theorem norm_regularCoefficients_le (u : BernoulliL2) : ‖regularCoefficients u‖ ≤ ‖u‖ := by
  have hs := tsum_comp_le_tsum_of_inj
    (show Summable (fun S => (walshBasis.repr u S) ^ 2) by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
        (lp.memℓp (walshBasis.repr u)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))
    (fun S => sq_nonneg _) regularIndex_injective
  have hnorm : ‖regularCoefficients u‖ ^ 2 ≤ ‖walshBasis.repr u‖ ^ 2 := by
    rw [coordinate_norm_sq, coordinate_norm_sq]
    exact hs
  rw [walshBasis.repr.norm_map] at hnorm
  nlinarith [norm_nonneg (regularCoefficients u), norm_nonneg u]

theorem norm_regularCoefficients_eq (u : BernoulliL2) (hmean : (∫ x, u x ∂bernoulli) = 0) :
    ‖regularCoefficients u‖ = ‖u‖ := by
  have hempty : walshBasis.repr u ∅ = 0 := (empty_walsh_coefficient u).trans hmean
  let b := fun S : Finset Group => (walshBasis.repr u S) ^ 2
  have hsupport : Function.support b ⊆ {S : Finset Group | S.Nonempty} := by
    intro S hS
    by_contra hne
    have heq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst S
    exact hS (by simp [b, hempty])
  have hsub : (∑' S : NonemptySupport, b S.val) = ∑' S : Finset Group, b S :=
    tsum_subtype_eq_of_support_subset hsupport
  have hreindex : (∑' p : SupportOrbit × Group, b (regularIndex p)) =
      ∑' S : NonemptySupport, b S.val :=
    supportOrbitEquiv.symm.tsum_eq (fun S : NonemptySupport => b S.val)
  have hnorm : ‖regularCoefficients u‖ ^ 2 = ‖walshBasis.repr u‖ ^ 2 := by
    rw [coordinate_norm_sq, coordinate_norm_sq]
    exact hreindex.trans hsub
  rw [walshBasis.repr.norm_map] at hnorm
  nlinarith [norm_nonneg (regularCoefficients u), norm_nonneg u]

theorem regularCoefficients_sub (u v : BernoulliL2) :
    regularCoefficients (u - v) = regularCoefficients u - regularCoefficients v := by
  ext p
  change walshBasis.repr (u - v) (regularIndex p) =
    walshBasis.repr u (regularIndex p) - walshBasis.repr v (regularIndex p)
  rw [map_sub]
  rfl

theorem regularCoefficients_koopman (a : Letter) (u : BernoulliL2) :
    regularCoefficients (koopman (letterGroup a) u) =
      permute (leftPermutation a) (regularCoefficients u) := by
  ext p
  rcases p with ⟨q, h⟩
  change walshBasis.repr (koopman (letterGroup a) u) (regularIndex (q, h)) =
    walshBasis.repr u (regularIndex (q, (letterGroup a)⁻¹ * h))
  rw [walsh_coefficient_koopman]
  have hv := congrArg Subtype.val (supportOrbitEquiv_symm_mul q (letterGroup a)⁻¹ h)
  exact congrArg (fun S : Finset Group => walshBasis.repr u S) hv.symm

theorem bernoulli_L2_spectral_gap (u : BernoulliL2) (hmean : (∫ x, u x ∂bernoulli) = 0) :
    ‖u‖ ^ 2 ≤ 8 *
      (‖koopman (letterGroup (0, true)) u - u‖ ^ 2 +
        ‖koopman (letterGroup (1, true)) u - u‖ ^ 2) := by
  have hgap := regular_free_group_gap (regularCoefficients u)
  have hA : permute (leftPermutation (0, true)) (regularCoefficients u) - regularCoefficients u =
      regularCoefficients (koopman (letterGroup (0, true)) u - u) := by
    rw [regularCoefficients_sub, regularCoefficients_koopman]
  have hB : permute (leftPermutation (1, true)) (regularCoefficients u) - regularCoefficients u =
      regularCoefficients (koopman (letterGroup (1, true)) u - u) := by
    rw [regularCoefficients_sub, regularCoefficients_koopman]
  rw [norm_regularCoefficients_eq u hmean, hA, hB] at hgap
  have hca := norm_regularCoefficients_le (koopman (letterGroup (0, true)) u - u)
  have hcb := norm_regularCoefficients_le (koopman (letterGroup (1, true)) u - u)
  nlinarith [norm_nonneg (regularCoefficients (koopman (letterGroup (0, true)) u - u)),
    norm_nonneg (regularCoefficients (koopman (letterGroup (1, true)) u - u)),
    norm_nonneg (koopman (letterGroup (0, true)) u - u),
    norm_nonneg (koopman (letterGroup (1, true)) u - u)]

end BenchmarkShift
end
end Source22
end BenchmarkCountableProof

/- Whole source module: BernoulliIsoperimetry -/
namespace BenchmarkCountableProof
section Source23
/-! A concrete measured expansion estimate for the two-generator Bernoulli shift. -/

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace symmDiff

noncomputable section

namespace BenchmarkShift

def constantL2 (c : ℝ) : BernoulliL2 := Lp.const 2 bernoulli c

lemma constantL2_ae (c : ℝ) : (constantL2 c : Point → ℝ) =ᵐ[bernoulli] fun _ => c :=
  Lp.coeFn_const _ _ _

lemma norm_constantL2 (c : ℝ) : ‖constantL2 c‖ = |c| := by
  simp [constantL2, Lp.norm_const' 2 bernoulli c (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]

lemma inner_constantL2_one (u : BernoulliL2) :
    ⟪constantL2 1, u⟫_ℝ = ∫ x, u x ∂bernoulli := by
  rw [constantL2, ← indicatorConstLp_univ]
  simpa using L2.inner_indicatorConstLp_one MeasurableSet.univ
    (measure_ne_top bernoulli univ) u

lemma constantL2_smul (c : ℝ) : constantL2 c = c • constantL2 1 := by
  apply Lp.ext
  filter_upwards [constantL2_ae c, constantL2_ae 1,
    Lp.coeFn_smul c (constantL2 1)] with x hx hy hz
  simp only [hx, hz, Pi.smul_apply, smul_eq_mul, hy, mul_one]

lemma koopman_constantL2 (g : Group) (c : ℝ) : koopman g (constantL2 c) = constantL2 c := by
  apply Lp.ext
  filter_upwards [koopman_ae g (constantL2 c), constantL2_ae c,
    (measurePreserving_shift g⁻¹).quasiMeasurePreserving.ae (constantL2_ae c)] with x hx hy hz
  exact hx.trans (hz.trans hy.symm)

theorem bernoulli_variance_gap (u : BernoulliL2) :
    ‖u‖ ^ 2 - (∫ x, u x ∂bernoulli) ^ 2 ≤ 8 *
      (‖koopman (letterGroup (0, true)) u - u‖ ^ 2 +
        ‖koopman (letterGroup (1, true)) u - u‖ ^ 2) := by
  let m := ∫ x, u x ∂bernoulli
  let v := u - constantL2 m
  have hinner : ⟪constantL2 1, v⟫_ℝ = 0 := by
    dsimp only [v]
    rw [inner_sub_right, constantL2_smul m, inner_smul_right]
    rw [inner_self_eq_norm_sq_to_K, norm_constantL2, inner_constantL2_one]
    norm_num [m]
  have hmean : (∫ x, v x ∂bernoulli) = 0 := by
    rw [← inner_constantL2_one]
    exact hinner
  have hnorm : ‖v‖ ^ 2 = ‖u‖ ^ 2 - m ^ 2 := by
    dsimp only [v]
    rw [norm_sub_sq_real, norm_constantL2, constantL2_smul m,
      inner_smul_right, real_inner_comm, inner_constantL2_one]
    rw [sq_abs]
    ring
  have hdiff (g : Group) : koopman g v - v = koopman g u - u := by
    dsimp only [v]
    rw [map_sub, koopman_constantL2]
    abel
  have hgap := bernoulli_L2_spectral_gap v hmean
  rwa [hnorm, hdiff, hdiff] at hgap

def indicatorL2 (s : Set Point) (hs : MeasurableSet s) : BernoulliL2 :=
  indicatorConstLp 2 hs (measure_ne_top bernoulli s) (1 : ℝ)

lemma norm_sq_indicatorL2 (s : Set Point) (hs : MeasurableSet s) :
    ‖indicatorL2 s hs‖ ^ 2 = bernoulli.real s := by
  rw [← real_inner_self_eq_norm_sq]
  simpa [indicatorL2] using L2.real_inner_indicatorConstLp_one_indicatorConstLp_one hs hs

lemma integral_indicatorL2 (s : Set Point) (hs : MeasurableSet s) :
    (∫ x, indicatorL2 s hs x ∂bernoulli) = bernoulli.real s := by
  rw [← inner_constantL2_one, constantL2, ← indicatorConstLp_univ]
  simpa [indicatorL2] using
    L2.real_inner_indicatorConstLp_one_indicatorConstLp_one MeasurableSet.univ hs
      (μ := bernoulli)

lemma koopman_indicatorL2 (g : Group) (s : Set Point) (hs : MeasurableSet s) :
    koopman g (indicatorL2 s hs) =
      indicatorL2 ((shift g⁻¹) ⁻¹' s) (hs.preimage (continuous_shift g⁻¹).measurable) := by
  apply Lp.ext
  have ht := (measurePreserving_shift g⁻¹).quasiMeasurePreserving.ae
    (indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs)
      (hμs := measure_ne_top bernoulli s) (c := (1 : ℝ)))
  filter_upwards [koopman_ae g (indicatorL2 s hs), ht,
    (indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
      (hs := hs.preimage (continuous_shift g⁻¹).measurable)
      (hμs := measure_ne_top bernoulli _) (c := (1 : ℝ)))] with x hx hy hz
  exact hx.trans (hy.trans (by simpa only [Set.indicator_comp_right] using hz.symm))

lemma norm_sq_indicatorL2_sub (s t : Set Point) (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    ‖indicatorL2 s hs - indicatorL2 t ht‖ ^ 2 = bernoulli.real (s ∆ t) := by
  rw [← dist_eq_norm, indicatorL2, indicatorL2, dist_indicatorConstLp_eq_norm]
  exact norm_sq_indicatorL2 (s ∆ t) (hs.symmDiff ht)

theorem bernoulli_set_expansion (s : Set Point) (hs : MeasurableSet s)
    (hsmall : bernoulli.real s ≤ 1 / 2) :
    bernoulli.real s ≤ 16 *
      (bernoulli.real (((shift (letterGroup (0, true))⁻¹) ⁻¹' s) ∆ s) +
       bernoulli.real (((shift (letterGroup (1, true))⁻¹) ⁻¹' s) ∆ s)) := by
  have hgap := bernoulli_variance_gap (indicatorL2 s hs)
  rw [norm_sq_indicatorL2, integral_indicatorL2, koopman_indicatorL2,
    koopman_indicatorL2, norm_sq_indicatorL2_sub, norm_sq_indicatorL2_sub] at hgap
  have hnonneg : 0 ≤ bernoulli.real s := ENNReal.toReal_nonneg
  nlinarith

end BenchmarkShift
end
end Source23
end BenchmarkCountableProof

/- Whole source module: BernoulliSupportGap -/
namespace BenchmarkCountableProof
section Source24
/-! The Hilbert gap for functions whose support has at most half the probability. -/

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace

noncomputable section

namespace BenchmarkShift

theorem bernoulli_supported_L2_gap (s : Set Point) (hs : MeasurableSet s)
    (hsmall : bernoulli.real s ≤ 1 / 2) (u : BernoulliL2)
    (hu : ∀ᵐ x ∂bernoulli, x ∉ s → u x = 0) :
    ‖u‖ ^ 2 ≤ 16 *
      (‖koopman (letterGroup (0, true)) u - u‖ ^ 2 +
        ‖koopman (letterGroup (1, true)) u - u‖ ^ 2) := by
  have hi : ⟪indicatorL2 s hs, u⟫_ℝ = ∫ x, u x ∂bernoulli := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu, (indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs)
      (hμs := measure_ne_top bernoulli s) (c := (1 : ℝ)))] with x hx hy
    simp only [RCLike.inner_apply, conj_trivial]
    rw [mul_comm]
    change indicatorConstLp 2 hs (measure_ne_top bernoulli s) (1 : ℝ) x * u x = u x
    rw [hy]
    by_cases hxs : x ∈ s
    · simp [hxs]
    · simp [hxs, hx hxs]
  have hcs := real_inner_mul_inner_self_le (indicatorL2 s hs) u
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_sq_indicatorL2, hi] at hcs
  have hm : (∫ x, u x ∂bernoulli) ^ 2 ≤ (1 / 2 : ℝ) * ‖u‖ ^ 2 := by
    have hb := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖u‖)
    nlinarith
  have hg := bernoulli_variance_gap u
  linarith

lemma norm_sq_L2_eq_integral (u : BernoulliL2) :
    ‖u‖ ^ 2 = ∫ x, (u x) ^ 2 ∂bernoulli := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  ext x
  simp [pow_two]

def inverseGeneratorShift (i : Fin 2) : Point → Point := shift (letterGroup (i, true))⁻¹

theorem supported_integral_sq_gap (f : Point → ℝ) (hf : Measurable f)
    (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hsmall : bernoulli.real {x | f x ≠ 0} ≤ 1 / 2) :
    (∫ x, (f x) ^ 2 ∂bernoulli) ≤ 16 *
      ((∫ x, (f (inverseGeneratorShift 0 x) - f x) ^ 2 ∂bernoulli) +
       (∫ x, (f (inverseGeneratorShift 1 x) - f x) ^ 2 ∂bernoulli)) := by
  obtain ⟨B, hB⟩ := hb
  have hmem : MemLp f 2 bernoulli := MemLp.of_bound hf.aestronglyMeasurable B
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hB x)
  let u : BernoulliL2 := hmem.toLp f
  have hu : (u : Point → ℝ) =ᵐ[bernoulli] f := hmem.coeFn_toLp
  have hs : MeasurableSet {x | f x ≠ 0} := (measurableSet_eq_fun hf measurable_const).compl
  have hsupport : ∀ᵐ x ∂bernoulli, x ∉ {x | f x ≠ 0} → u x = 0 := by
    filter_upwards [hu] with x hx
    simpa only [mem_setOf_eq, not_not, hx] using (fun h : f x = 0 => h)
  have hg := bernoulli_supported_L2_gap {x | f x ≠ 0} hs hsmall u hsupport
  have hn : ‖u‖ ^ 2 = ∫ x, (f x) ^ 2 ∂bernoulli := by
    rw [norm_sq_L2_eq_integral]
    exact integral_congr_ae (hu.fun_comp fun y : ℝ => y ^ 2)
  have hd (i : Fin 2) : ‖koopman (letterGroup (i, true)) u - u‖ ^ 2 =
      ∫ x, (f (inverseGeneratorShift i x) - f x) ^ 2 ∂bernoulli := by
    rw [norm_sq_L2_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (koopman (letterGroup (i, true)) u) u,
      koopman_ae (letterGroup (i, true)) u, hu,
      (measurePreserving_shift (letterGroup (i, true))⁻¹).quasiMeasurePreserving.ae hu]
      with x hx hy hz hw
    change (koopman (letterGroup (i, true)) u - u) x ^ 2 = _
    rw [hx, Pi.sub_apply, hy, hz, hw]
    rfl
  rwa [hn, hd, hd] at hg

end BenchmarkShift
end
end Source24
end BenchmarkCountableProof

/- Whole source module: PowerDifference -/
namespace BenchmarkCountableProof
section Source25
/-! Elementary power estimates used to transfer the Hilbert gap to every finite exponent. -/

open Set

noncomputable section

namespace BenchmarkPowerDifference

theorem abs_sub_rpow_le {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : |a ^ q - b ^ q| ≤ |a - b| ^ q := by
  wlog hab : b ≤ a generalizing a b
  · simpa only [abs_sub_comm] using this hb ha (le_of_not_ge hab)
  have hpow := Real.rpow_add_le_add_rpow hb (sub_nonneg.mpr hab) hq0 hq1
  have hmon := Real.rpow_le_rpow hb hab hq0
  rw [add_sub_cancel] at hpow
  rw [abs_of_nonneg (sub_nonneg.mpr hmon), abs_of_nonneg (sub_nonneg.mpr hab)]
  linarith

theorem abs_sub_rpow_le_lipschitz {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq : 1 ≤ q) : |a ^ q - b ^ q| ≤ q * (max a b) ^ (q - 1) * |a - b| := by
  have hd (x : ℝ) (_ : x ∈ Icc 0 (max a b)) :
      HasDerivWithinAt (fun x : ℝ => x ^ q) (q * x ^ (q - 1)) (Icc 0 (max a b)) x :=
    (Real.hasDerivAt_rpow_const (Or.inr hq)).hasDerivWithinAt
  have hbound (x : ℝ) (hx : x ∈ Icc 0 (max a b)) :
      ‖q * x ^ (q - 1)‖ ≤ q * (max a b) ^ (q - 1) := by
    rw [Real.norm_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hx.1 _))]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hx.1 hx.2 (sub_nonneg.mpr hq)) (by linarith)
  have h := (convex_Icc 0 (max a b)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hbound ⟨hb, le_max_right _ _⟩ ⟨ha, le_max_left _ _⟩
  simpa only [Real.norm_eq_abs] using h

def powerErrorConstant (p : ℝ) : ℝ := p ^ 2 * (16 * p) ^ (p - 2)

theorem powerErrorConstant_nonneg (p : ℝ) (hp : 2 ≤ p) : 0 ≤ powerErrorConstant p := by
  unfold powerErrorConstant
  positivity

theorem power_difference_sq_le {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 2 ≤ p) :
    (a ^ (p / 2) - b ^ (p / 2)) ^ 2 ≤
      (1 / 256 : ℝ) * (max a b) ^ p + powerErrorConstant p * |a - b| ^ p := by
  let M := max a b
  let d := |a - b|
  have hM : 0 ≤ M := le_trans ha (le_max_left _ _)
  have hd : 0 ≤ d := abs_nonneg _
  have hp0 : 0 < p := by linarith
  have he : 0 ≤ p - 2 := by linarith
  have hbasic := abs_sub_rpow_le_lipschitz ha hb (q := p / 2) (by linarith)
  have hsquare : (a ^ (p / 2) - b ^ (p / 2)) ^ 2 ≤
      p ^ 2 * M ^ (p - 2) * d ^ 2 := by
    have hpow : (M ^ (p / 2 - 1)) ^ 2 = M ^ (p - 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hM]
      congr 1
      ring
    have hsq := sq_le_sq₀ (abs_nonneg (a ^ (p / 2) - b ^ (p / 2)))
      (mul_nonneg (mul_nonneg (by linarith : 0 ≤ p / 2) (Real.rpow_nonneg hM _)) hd) |>.mpr hbasic
    rw [sq_abs, mul_pow, mul_pow, hpow] at hsq
    have hn : 0 ≤ M ^ (p - 2) * d ^ 2 := by positivity
    dsimp only [M, d] at hsq ⊢
    nlinarith
  have hsum : M ^ (p - 2) * M ^ 2 = M ^ p := by
    rw [← Real.rpow_natCast M 2]
    norm_num only [Nat.cast_ofNat]
    rw [← Real.rpow_add_of_nonneg hM he (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  by_cases hsmall : d ≤ M / (16 * p)
  · have hscale : d * (16 * p) ≤ M := (le_div_iff₀ (by positivity)).mp hsmall
    have hs : p ^ 2 * d ^ 2 ≤ M ^ 2 / 256 := by
      have hsqr := (sq_le_sq₀ (by positivity : 0 ≤ d * (16 * p)) hM).mpr hscale
      nlinarith
    have hbnd := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hM (p - 2))
    have hfinish : p ^ 2 * M ^ (p - 2) * d ^ 2 ≤ (1 / 256 : ℝ) * M ^ p := by
      rw [← hsum]
      nlinarith
    exact hsquare.trans (hfinish.trans (le_add_of_nonneg_right
      (mul_nonneg (powerErrorConstant_nonneg p hp) (Real.rpow_nonneg hd _))))
  · have hlarge : M ≤ (16 * p) * d := by
      have h := (div_lt_iff₀ (by positivity : 0 < 16 * p)).mp (lt_of_not_ge hsmall)
      linarith
    have hpow := Real.rpow_le_rpow hM hlarge he
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 16 * p) hd] at hpow
    have hsumd : d ^ (p - 2) * d ^ 2 = d ^ p := by
      rw [← Real.rpow_natCast d 2]
      norm_num only [Nat.cast_ofNat]
      rw [← Real.rpow_add_of_nonneg hd he (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    have hmul := mul_le_mul_of_nonneg_left hpow (mul_nonneg (sq_nonneg p) (sq_nonneg d))
    have hfinish : p ^ 2 * M ^ (p - 2) * d ^ 2 ≤ powerErrorConstant p * d ^ p := by
      unfold powerErrorConstant
      rw [← hsumd]
      nlinarith
    exact hsquare.trans (hfinish.trans (le_add_of_nonneg_left
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hM _))))

end BenchmarkPowerDifference
end
end Source25
end BenchmarkCountableProof

/- Whole source module: BernoulliPowerGap -/
namespace BenchmarkCountableProof
section Source26
/-! Transfer of the actual Bernoulli Hilbert gap to nonnegative bounded functions
supported on a set of probability at most one half. The power estimate uses
an absorption inequality, so no unproved interpolation theorem is assumed. -/

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace

noncomputable section

namespace BenchmarkShift

lemma bounded_power (f : Point → ℝ) (hn : ∀ x, 0 ≤ f x)
    (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B) (q : ℝ) (hq : 0 ≤ q) :
    ∃ B : ℝ, ∀ x, |(f x) ^ q| ≤ B := by
  obtain ⟨B, hB⟩ := hb
  refine ⟨(max B 0) ^ q, fun x => ?_⟩
  rw [abs_of_nonneg (Real.rpow_nonneg (hn x) _)]
  exact Real.rpow_le_rpow (hn x) ((le_abs_self _).trans ((hB x).trans (le_max_left _ _))) hq

lemma bounded_integrable (f : Point → ℝ) (hf : Measurable f)
    (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B) : Integrable f bernoulli := by
  obtain ⟨B, hB⟩ := hb
  exact (MemLp.of_bound (p := (1 : ℝ≥0∞)) hf.aestronglyMeasurable B
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hB x)).integrable le_rfl

lemma bounded_power_integrable (f : Point → ℝ) (hf : Measurable f)
    (hn : ∀ x, 0 ≤ f x) (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B) (q : ℝ) (hq : 0 ≤ q) :
    Integrable (fun x => f x ^ q) bernoulli :=
  bounded_integrable _ ((Real.continuous_rpow_const hq).measurable.comp hf)
    (bounded_power f hn hb q hq)

lemma bounded_difference (f : Point → ℝ) (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (t : Point → Point) : ∃ B : ℝ, ∀ x, |f (t x) - f x| ≤ B := by
  obtain ⟨B, hB⟩ := hb
  exact ⟨2 * B, fun x => (abs_sub _ _).trans (by linarith [hB (t x), hB x])⟩

lemma bounded_difference_power_integrable (f : Point → ℝ) (hf : Measurable f)
    (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B) (t : Point → Point) (ht : Measurable t)
    (p : ℝ) (hp : 0 ≤ p) : Integrable (fun x => |f (t x) - f x| ^ p) bernoulli := by
  apply bounded_power_integrable _ ((hf.comp ht).sub hf).abs (fun x => abs_nonneg _) _ p hp
  simpa only [abs_abs] using bounded_difference f hb t

lemma integral_shift (g : Group) (f : Point → ℝ) :
    (∫ x, f (shift g x) ∂bernoulli) = ∫ x, f x ∂bernoulli := by
  have hfun : shift g = (MeasurableEquiv.piCongrLeft (fun _ : Group => Bool) (Equiv.mulLeft g)) := by
    funext x h
    obtain ⟨k, rfl⟩ := (Equiv.mulLeft g).surjective h
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    simp [shift]
  exact (measurePreserving_shift g).integral_comp
    (hfun ▸ (MeasurableEquiv.piCongrLeft (fun _ : Group => Bool) (Equiv.mulLeft g)).measurableEmbedding) f

def powerGapConstant (p : ℝ) : ℝ :=
  if p ≤ 2 then 16 else 32 * BenchmarkPowerDifference.powerErrorConstant p

lemma powerGapConstant_nonneg {p : ℝ} (hp : 0 < p) : 0 ≤ powerGapConstant p := by
  unfold powerGapConstant
  split_ifs with h
  · norm_num
  · exact mul_nonneg (by norm_num)
      (BenchmarkPowerDifference.powerErrorConstant_nonneg p (by linarith))

theorem supported_integral_power_gap (p : ℝ) (hp : 0 < p)
    (f : Point → ℝ) (hf : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hsmall : bernoulli.real {x | f x ≠ 0} ≤ 1 / 2) :
    (∫ x, (f x) ^ p ∂bernoulli) ≤ powerGapConstant p *
      ((∫ x, |f (inverseGeneratorShift 0 x) - f x| ^ p ∂bernoulli) +
       (∫ x, |f (inverseGeneratorShift 1 x) - f x| ^ p ∂bernoulli)) := by
  let h : Point → ℝ := fun x => f x ^ (p / 2)
  have hq : 0 < p / 2 := by linarith
  have hh : Measurable h := (Real.continuous_rpow_const hq.le).measurable.comp hf
  have hhb := bounded_power f hn hb (p / 2) hq.le
  have hhs : {x | h x ≠ 0} = {x | f x ≠ 0} := by
    ext x
    exact Real.rpow_ne_zero (hn x) hq.ne'
  have hg := supported_integral_sq_gap h hh hhb (hhs ▸ hsmall)
  have hsq (x : Point) : h x ^ 2 = f x ^ p := by
    dsimp only [h]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hn x)]
    congr 1
    norm_num
  simp_rw [hsq] at hg
  by_cases hp2 : p ≤ 2
  · have hbound (i : Fin 2) :
        (∫ x, (h (inverseGeneratorShift i x) - h x) ^ 2 ∂bernoulli) ≤
          ∫ x, |f (inverseGeneratorShift i x) - f x| ^ p ∂bernoulli := by
      apply integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
        (bounded_difference_power_integrable f hf hb _ (continuous_shift _).measurable p hp.le)
      apply ae_of_all
      intro x
      have he := BenchmarkPowerDifference.abs_sub_rpow_le
        (hn (inverseGeneratorShift i x)) (hn x) hq.le (by linarith : p / 2 ≤ 1)
      have h2 := (sq_le_sq₀ (abs_nonneg _)
        (Real.rpow_nonneg (abs_nonneg (f (inverseGeneratorShift i x) - f x)) _)).mpr he
      have heq : (|f (inverseGeneratorShift i x) - f x| ^ (p / 2)) ^ 2 =
          |f (inverseGeneratorShift i x) - f x| ^ p := by
        rw [← Real.rpow_natCast (|f (inverseGeneratorShift i x) - f x| ^ (p / 2)) 2,
          ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        norm_num
      rw [sq_abs, heq] at h2
      exact h2
    have h0 := hbound 0
    have h1 := hbound 1
    simp only [powerGapConstant, if_pos hp2]
    linarith
  · have hp2' : 2 ≤ p := le_of_lt (lt_of_not_ge hp2)
    let C := BenchmarkPowerDifference.powerErrorConstant p
    let I := ∫ x, f x ^ p ∂bernoulli
    have hI : 0 ≤ I := integral_nonneg fun x => Real.rpow_nonneg (hn x) _
    have hC : 0 ≤ C := BenchmarkPowerDifference.powerErrorConstant_nonneg p hp2'
    have hbound (i : Fin 2) :
        (∫ x, (h (inverseGeneratorShift i x) - h x) ^ 2 ∂bernoulli) ≤
          (1 / 128 : ℝ) * I + C *
            ∫ x, |f (inverseGeneratorShift i x) - f x| ^ p ∂bernoulli := by
      have hfpi := bounded_power_integrable f hf hn hb p hp.le
      have hs : Integrable (fun x => f (inverseGeneratorShift i x) ^ p) bernoulli :=
        bounded_power_integrable _ (hf.comp (continuous_shift _).measurable)
          (fun x => hn _) (by
            obtain ⟨B, hB⟩ := hb
            exact ⟨B, fun x => hB _⟩) p hp.le
      have hd := bounded_difference_power_integrable f hf hb (inverseGeneratorShift i)
        (continuous_shift (letterGroup (i, true))⁻¹).measurable p hp.le
      have hr := ((hs.add hfpi).const_mul (1 / 256 : ℝ)).add (hd.const_mul C)
      have hle := integral_mono_of_nonneg (ae_of_all _ fun x =>
        sq_nonneg (h (inverseGeneratorShift i x) - h x)) hr (ae_of_all _ fun x => ?_)
      · change (∫ x, (h (inverseGeneratorShift i x) - h x) ^ 2 ∂bernoulli) ≤
          ∫ x, (1 / 256 : ℝ) * (f (inverseGeneratorShift i x) ^ p + f x ^ p) +
            C * |f (inverseGeneratorShift i x) - f x| ^ p ∂bernoulli at hle
        have hadd := integral_add ((hs.add hfpi).const_mul (1 / 256 : ℝ)) (hd.const_mul C)
        have hadd' := integral_add hs hfpi
        simp only [Pi.add_apply] at hadd hadd'
        rw [hadd, integral_const_mul, hadd', integral_const_mul] at hle
        have hshift : (∫ x, f (inverseGeneratorShift i x) ^ p ∂bernoulli) = I :=
          integral_shift _ (fun x => f x ^ p)
        rw [hshift] at hle
        dsimp only [I] at hle ⊢
        linarith
      · have he := BenchmarkPowerDifference.power_difference_sq_le
          (hn (inverseGeneratorShift i x)) (hn x) hp2'
        have hm : (max (f (inverseGeneratorShift i x)) (f x)) ^ p ≤
            f (inverseGeneratorShift i x) ^ p + f x ^ p := by
          rcases le_total (f (inverseGeneratorShift i x)) (f x) with ht | ht
          · rw [max_eq_right ht]
            exact le_add_of_nonneg_left (Real.rpow_nonneg (hn _) _)
          · rw [max_eq_left ht]
            exact le_add_of_nonneg_right (Real.rpow_nonneg (hn _) _)
        change (f (inverseGeneratorShift i x) ^ (p / 2) - f x ^ (p / 2)) ^ 2 ≤
          (1 / 256 : ℝ) * (f (inverseGeneratorShift i x) ^ p + f x ^ p) +
            BenchmarkPowerDifference.powerErrorConstant p * |f (inverseGeneratorShift i x) - f x| ^ p
        linarith only [he, hm]
    have h0 := hbound 0
    have h1 := hbound 1
    have hD0 : 0 ≤ ∫ x, |f (inverseGeneratorShift 0 x) - f x| ^ p ∂bernoulli :=
      integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
    have hD1 : 0 ≤ ∫ x, |f (inverseGeneratorShift 1 x) - f x| ^ p ∂bernoulli :=
      integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
    simp only [powerGapConstant, if_neg hp2]
    change I ≤ 32 * C * _
    dsimp only [I] at h0 h1 ⊢
    nlinarith

end BenchmarkShift
end
end Source26
end BenchmarkCountableProof

/- Whole source module: RadialRetraction -/
namespace BenchmarkCountableProof
section Source27
/-! The radial truncation estimate used in the all-finite-p spectral-gap
argument.  This holds in every real normed space and uses no integrability
hypothesis on the vector being truncated. -/

noncomputable section

namespace BenchmarkRadial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radial (R : ℝ) (v : E) : E := (R / max R ‖v‖) • v

theorem norm_radial_le {R : ℝ} (hR : 0 < R) (v : E) :
    ‖radial R v‖ ≤ R := by
  have hA : 0 < max R ‖v‖ := lt_of_lt_of_le hR (le_max_left _ _)
  have ha : 0 ≤ R / max R ‖v‖ := div_nonneg hR.le hA.le
  rw [radial, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  calc
    R / max R ‖v‖ * ‖v‖ ≤ R / max R ‖v‖ * max R ‖v‖ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) ha
    _ = R := div_mul_cancel₀ _ hA.ne'

theorem radial_eq_self {R : ℝ} (hR : 0 < R) {v : E} (hv : ‖v‖ ≤ R) :
    radial R v = v := by
  simp [radial, max_eq_left hv, hR.ne']

lemma norm_radial_sub_le_ordered {R : ℝ} (hR : 0 < R) (v w : E)
    (hvw : ‖w‖ ≤ ‖v‖) :
    ‖radial R v - radial R w‖ ≤ 2 * ‖v - w‖ := by
  let A := max R ‖v‖
  let B := max R ‖w‖
  let a := R / A
  let b := R / B
  have hA : 0 < A := lt_of_lt_of_le hR (le_max_left _ _)
  have hB : 0 < B := lt_of_lt_of_le hR (le_max_left _ _)
  have hBA : B ≤ A := max_le_max_left R hvw
  have ha : 0 ≤ a := div_nonneg hR.le hA.le
  have ha1 : a ≤ 1 := (div_le_one hA).mpr (le_max_left _ _)
  have hab : a ≤ b := by
    change R / A ≤ R / B
    apply (div_le_div_iff₀ hA hB).mpr
    nlinarith
  have haA : a * A = R := div_mul_cancel₀ _ hA.ne'
  have hbB : b * B = R := div_mul_cancel₀ _ hB.ne'
  have hAB : A - B ≤ ‖v‖ - ‖w‖ := by
    dsimp [A, B]
    by_cases hv : ‖v‖ ≤ R
    · rw [max_eq_left hv, max_eq_left (hvw.trans hv)]
      linarith
    · rw [max_eq_right (le_of_not_ge hv)]
      have : ‖w‖ ≤ max R ‖w‖ := le_max_right _ _
      linarith
  have hD : ‖v‖ - ‖w‖ ≤ ‖v - w‖ := norm_sub_norm_le v w
  have hterm : (b - a) * ‖w‖ ≤ ‖v - w‖ := by
    calc
      (b - a) * ‖w‖ ≤ (b - a) * B :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (sub_nonneg.mpr hab)
      _ = a * (A - B) := by nlinarith [haA, hbB]
      _ ≤ A - B := by nlinarith [sub_nonneg.mpr hBA]
      _ ≤ ‖v - w‖ := hAB.trans hD
  have hdecomp : a • v - b • w = a • (v - w) + (a - b) • w := by
    simp only [smul_sub, sub_smul]
    abel
  change ‖a • v - b • w‖ ≤ _
  rw [hdecomp]
  calc
    ‖a • (v - w) + (a - b) • w‖ ≤ ‖a • (v - w)‖ + ‖(a - b) • w‖ := norm_add_le _ _
    _ = a * ‖v - w‖ + (b - a) * ‖w‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonpos (sub_nonpos.mpr hab)]
      ring
    _ ≤ 2 * ‖v - w‖ := by nlinarith [norm_nonneg (v - w)]

theorem norm_radial_sub_le {R : ℝ} (hR : 0 < R) (v w : E) :
    ‖radial R v - radial R w‖ ≤ 2 * ‖v - w‖ := by
  rcases le_total ‖w‖ ‖v‖ with h | h
  · exact norm_radial_sub_le_ordered hR v w h
  · simpa only [norm_sub_rev] using norm_radial_sub_le_ordered hR w v h

theorem norm_radial_sub_le_two_radius {R : ℝ} (hR : 0 < R) (v w : E) :
    ‖radial R v - radial R w‖ ≤ 2 * R := by
  calc
    ‖radial R v - radial R w‖ ≤ ‖radial R v‖ + ‖radial R w‖ := norm_sub_le _ _
    _ ≤ 2 * R := by linarith [norm_radial_le hR v, norm_radial_le hR w]

theorem norm_radial_sub_le_two_min {R : ℝ} (hR : 0 < R) (v w : E) :
    ‖radial R v - radial R w‖ ≤ 2 * min ‖v - w‖ R := by
  rcases le_total ‖v - w‖ R with h | h
  · rw [min_eq_left h]
    exact norm_radial_sub_le hR v w
  · rw [min_eq_right h]
    exact norm_radial_sub_le_two_radius hR v w

end BenchmarkRadial
end
end Source27
end BenchmarkCountableProof

/- Whole source module: RadialEnergy -/
namespace BenchmarkCountableProof
section Source28
/-! Finite-dimensional radial energy estimates. Scalar Poincaré
inequalities for the truncated coordinates imply the vector truncated
energy inequality. Neither the original vector nor its displacement
is required to be integrable. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

noncomputable section

namespace BenchmarkRadialEnergy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma continuous_radial {R : ℝ} (hR : 0 < R) : Continuous (BenchmarkRadial.radial R : E → E) := by
  apply Continuous.smul _ continuous_id
  apply continuous_const.div (continuous_const.max continuous_norm)
  intro v
  exact (lt_of_lt_of_le hR (le_max_left _ _)).ne'

lemma norm_radial_eq_min {R : ℝ} (hR : 0 < R) (v : E) :
    ‖BenchmarkRadial.radial R v‖ = min ‖v‖ R := by
  by_cases hv : ‖v‖ ≤ R
  · rw [BenchmarkRadial.radial_eq_self hR hv, min_eq_left hv]
  · have hnv : 0 < ‖v‖ := lt_of_lt_of_le hR (le_of_not_ge hv)
    rw [BenchmarkRadial.radial, max_eq_right (le_of_not_ge hv), min_eq_right (le_of_not_ge hv),
      norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR hnv)]
    exact div_mul_cancel₀ _ hnv.ne'

lemma min_rpow (a b q : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    (min a b) ^ q = min (a ^ q) (b ^ q) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, min_eq_left (Real.rpow_le_rpow ha hab hq)]
  · rw [min_eq_right hba, min_eq_right (Real.rpow_le_rpow hb hba hq)]

lemma radial_energy_bound {R q : ℝ} (hR : 0 < R) (hq : 0 ≤ q) (v w : E) :
    ENNReal.ofReal (‖BenchmarkRadial.radial R v - BenchmarkRadial.radial R w‖ ^ q) ≤
      ENNReal.ofReal ((2 : ℝ) ^ q) * ENNReal.ofReal (min (‖v - w‖ ^ q) (R ^ q)) := by
  have hb := Real.rpow_le_rpow (norm_nonneg _)
    (BenchmarkRadial.norm_radial_sub_le_two_min hR v w) hq
  rw [Real.mul_rpow (by norm_num) (le_min (norm_nonneg _) hR.le),
    min_rpow _ _ _ (norm_nonneg _) hR.le hq] at hb
  have he := ENNReal.ofReal_le_ofReal hb
  rwa [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)] at he

variable {I : Type*} [Fintype I] (p : ℝ≥0∞) [Fact (1 ≤ p)]

abbrev Vector := PiLp p (fun _ : I => ℝ)

def scalarEnergy (r : ℝ) : ℝ≥0∞ := ENNReal.ofReal (|r| ^ p.toReal)
def vectorEnergy (v : Vector (I := I) p) : ℝ≥0∞ := ENNReal.ofReal (‖v‖ ^ p.toReal)

lemma norm_rpow_eq_sum (hp : p ≠ ∞) (v : Vector (I := I) p) :
    ‖v‖ ^ p.toReal = ∑ i, |v i| ^ p.toReal := by
  have hpos : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
  rw [PiLp.norm_eq_sum hpos, ← Real.rpow_mul (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) ]
  rw [one_div_mul_cancel hpos.ne', Real.rpow_one]
  simp only [Real.norm_eq_abs]

lemma vectorEnergy_eq_sum (hp : p ≠ ∞) (v : Vector (I := I) p) :
    vectorEnergy p v = ∑ i, scalarEnergy p (v i) := by
  unfold vectorEnergy scalarEnergy
  rw [norm_rpow_eq_sum p hp]
  exact ENNReal.ofReal_sum_of_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _

variable {X S : Type*} [MeasurableSpace X] [Fintype S] (μ : Measure X)

lemma integral_vectorEnergy (hp : p ≠ ∞) (v : X → Vector (I := I) p) (hv : Measurable v) :
    (∫⁻ x, vectorEnergy p (v x) ∂μ) = ∑ i, ∫⁻ x, scalarEnergy p (v x i) ∂μ := by
  simp_rw [vectorEnergy_eq_sum p hp]
  apply lintegral_finsetSum
  intro i _
  exact ((((PiLp.continuous_apply p (β := fun _ : I => ℝ) i).measurable.comp hv).abs).pow_const _).ennreal_ofReal

/-- This is the finite-prefix truncated-energy inequality obtained by adding
the scalar Poincaré inequalities for the radial coordinates. -/
theorem truncated_energy_from_scalar
    (hp : p ≠ ∞) {R : ℝ} (hR : 0 < R) (C : ℝ≥0∞)
    (t : S → X → X) (ht : ∀ s, Measurable (t s))
    (v : X → Vector (I := I) p) (hv : Measurable v)
    (hscalar : ∀ i : I,
      (∫⁻ x, scalarEnergy p (BenchmarkRadial.radial R (v x) i) ∂μ) ≤
        C * ∑ s : S, ∫⁻ x, scalarEnergy p
          (BenchmarkRadial.radial R (v (t s x)) i - BenchmarkRadial.radial R (v x) i) ∂μ) :
    (∫⁻ x, ENNReal.ofReal (min (‖v x‖ ^ p.toReal) (R ^ p.toReal)) ∂μ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ p.toReal) * C *
        ∑ s : S, ∫⁻ x, ENNReal.ofReal (min (‖v (t s x) - v x‖ ^ p.toReal) (R ^ p.toReal)) ∂μ := by
  classical
  let u := fun x => BenchmarkRadial.radial R (v x)
  have hu : Measurable u := continuous_radial hR |>.measurable.comp hv
  have hleft : (∫⁻ x, ENNReal.ofReal (min (‖v x‖ ^ p.toReal) (R ^ p.toReal)) ∂μ) =
      ∑ i, ∫⁻ x, scalarEnergy p (u x i) ∂μ := by
    rw [← integral_vectorEnergy p μ hp u hu]
    congr 1
    funext x
    unfold vectorEnergy
    rw [norm_radial_eq_min hR, min_rpow _ _ _ (norm_nonneg _) hR.le ENNReal.toReal_nonneg]
  have hmiddle : (∑ i, C * ∑ s : S, ∫⁻ x, scalarEnergy p (u (t s x) i - u x i) ∂μ) =
      C * ∑ s : S, ∫⁻ x, vectorEnergy p (u (t s x) - u x) ∂μ := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    exact (integral_vectorEnergy p μ hp (fun x => u (t s x) - u x)
      ((hu.comp (ht s)).sub hu)).symm
  have hbound : ∀ s : S,
      (∫⁻ x, vectorEnergy p (u (t s x) - u x) ∂μ) ≤
        ENNReal.ofReal ((2 : ℝ) ^ p.toReal) *
          ∫⁻ x, ENNReal.ofReal (min (‖v (t s x) - v x‖ ^ p.toReal) (R ^ p.toReal)) ∂μ := by
    intro s
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro x
    exact radial_energy_bound hR ENNReal.toReal_nonneg (v (t s x)) (v x)
  calc
    _ = ∑ i, ∫⁻ x, scalarEnergy p (u x i) ∂μ := hleft
    _ ≤ ∑ i, C * ∑ s : S, ∫⁻ x, scalarEnergy p (u (t s x) i - u x i) ∂μ :=
      Finset.sum_le_sum fun i _ => hscalar i
    _ = C * ∑ s : S, ∫⁻ x, vectorEnergy p (u (t s x) - u x) ∂μ := hmiddle
    _ ≤ C * ∑ s : S, ENNReal.ofReal ((2 : ℝ) ^ p.toReal) *
        ∫⁻ x, ENNReal.ofReal (min (‖v (t s x) - v x‖ ^ p.toReal) (R ^ p.toReal)) ∂μ :=
      mul_le_mul_left' (Finset.sum_le_sum fun s _ => hbound s) C
    _ = _ := by rw [← Finset.mul_sum]; ac_rfl

end BenchmarkRadialEnergy
end
end Source28
end BenchmarkCountableProof

/- Whole source module: PoincareRadial -/
namespace BenchmarkCountableProof
section Source29
/-! Applying a scalar median Poincaré bound to radial truncations. Strict
positivity of the radial multiplier preserves the positive and negative
sets of every coordinate, so the medians remain zero. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

noncomputable section

namespace BenchmarkPoincareRadial

variable {X S I : Type*} [MeasurableSpace X] [Fintype S] [Fintype I]

def ZeroMedian (μ : Measure X) (f : X → ℝ) : Prop :=
  μ {x | f x < 0} ≤ μ univ / 2 ∧ μ {x | 0 < f x} ≤ μ univ / 2

def ScalarPoincareBound (p : ℝ≥0∞) (μ : Measure X) (t : S → X → X) (C : ℝ≥0∞) : Prop :=
  ∀ f : X → ℝ, Measurable f → ZeroMedian μ f →
    (∃ B : ℝ, ∀ x, |f x| ≤ B) →
    (∫⁻ x, BenchmarkRadialEnergy.scalarEnergy p (f x) ∂μ) ≤
      C * ∑ s : S, ∫⁻ x, BenchmarkRadialEnergy.scalarEnergy p (f (t s x) - f x) ∂μ

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure X)

theorem zeroMedian_radial_coordinate {R : ℝ} (hR : 0 < R)
    (v : X → BenchmarkRadialEnergy.Vector (I := I) p) (i : I)
    (hm : ZeroMedian μ (fun x => v x i)) :
    ZeroMedian μ (fun x => BenchmarkRadial.radial R (v x) i) := by
  have hc : ∀ x, 0 < R / max R ‖v x‖ := fun x =>
    div_pos hR (lt_of_lt_of_le hR (le_max_left _ _))
  have hneg : {x | BenchmarkRadial.radial R (v x) i < 0} = {x | v x i < 0} := by
    ext x
    simp only [mem_setOf_eq, BenchmarkRadial.radial, PiLp.smul_apply, smul_eq_mul]
    constructor
    · intro h
      by_contra hb
      have hb0 : 0 ≤ v x i := le_of_not_gt hb
      have hh := mul_nonneg (hc x).le hb0
      linarith
    · intro h
      have hh := mul_pos (hc x) (neg_pos.mpr h)
      nlinarith
  have hpos : {x | 0 < BenchmarkRadial.radial R (v x) i} = {x | 0 < v x i} := by
    ext x
    simp only [mem_setOf_eq, BenchmarkRadial.radial, PiLp.smul_apply, smul_eq_mul]
    exact mul_pos_iff_of_pos_left (hc x)
  unfold ZeroMedian at hm ⊢
  rwa [hneg, hpos]

theorem truncated_energy_of_poincare
    (hp : p ≠ ∞) {R : ℝ} (hR : 0 < R) (C : ℝ≥0∞)
    (t : S → X → X) (ht : ∀ s, Measurable (t s))
    (hP : ScalarPoincareBound p μ t C)
    (v : X → BenchmarkRadialEnergy.Vector (I := I) p) (hv : Measurable v)
    (hm : ∀ i, ZeroMedian μ (fun x => v x i)) :
    (∫⁻ x, ENNReal.ofReal (min (‖v x‖ ^ p.toReal) (R ^ p.toReal)) ∂μ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ p.toReal) * C *
        ∑ s : S, ∫⁻ x, ENNReal.ofReal (min (‖v (t s x) - v x‖ ^ p.toReal) (R ^ p.toReal)) ∂μ := by
  apply BenchmarkRadialEnergy.truncated_energy_from_scalar p μ hp hR C t ht v hv
  intro i
  apply hP
  · exact (PiLp.continuous_apply p (β := fun _ : I => ℝ) i).measurable.comp
      ((BenchmarkRadialEnergy.continuous_radial hR).measurable.comp hv)
  · exact zeroMedian_radial_coordinate p μ hR v i (hm i)
  · refine ⟨R, fun x => ?_⟩
    have hb := (PiLp.norm_apply_le (p := p) (BenchmarkRadial.radial R (v x)) i).trans
      (BenchmarkRadial.norm_radial_le hR (v x))
    simpa only [Real.norm_eq_abs] using hb

end BenchmarkPoincareRadial
end
end Source29
end BenchmarkCountableProof

/- Whole source module: BernoulliMedianGap -/
namespace BenchmarkCountableProof
section Source30
/-! A median Poincaré inequality for every finite positive exponent, with an
explicit finite constant, on the actual Bernoulli action of the free group. -/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkShift

lemma measureReal_le_half {s : Set Point} (h : bernoulli s ≤ 1 / 2) :
    bernoulli.real s ≤ (1 / 2 : ℝ) := by
  have hh := ENNReal.toReal_mono (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ∞) h
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at hh
  exact hh

lemma positivePart_support (f : Point → ℝ) :
    {x | max (f x) 0 ≠ 0} = {x | 0 < f x} := by
  ext x
  by_cases hx : 0 < f x
  · simp [hx, max_eq_left hx.le, hx.ne']
  · simp [hx, max_eq_right (le_of_not_gt hx)]

lemma bounded_positivePart (f : Point → ℝ) (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B) :
    ∃ B : ℝ, ∀ x, |max (f x) 0| ≤ B := by
  obtain ⟨B, hB⟩ := hb
  refine ⟨B, fun x => ?_⟩
  have h := abs_max_sub_max_le_abs (f x) 0 0
  have h' : |max (f x) 0| ≤ |f x| := by simpa only [max_self, sub_zero] using h
  exact h'.trans (hB x)

theorem median_integral_power_gap (p : ℝ) (hp : 0 < p)
    (f : Point → ℝ) (hf : Measurable f)
    (hm : BenchmarkPoincareRadial.ZeroMedian bernoulli f)
    (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B) :
    (∫ x, |f x| ^ p ∂bernoulli) ≤ (2 * powerGapConstant p) *
      ((∫ x, |f (inverseGeneratorShift 0 x) - f x| ^ p ∂bernoulli) +
       (∫ x, |f (inverseGeneratorShift 1 x) - f x| ^ p ∂bernoulli)) := by
  let fpos : Point → ℝ := fun x => max (f x) 0
  let fneg : Point → ℝ := fun x => max (-f x) 0
  have hfpos : Measurable fpos := hf.max measurable_const
  have hfneg : Measurable fneg := hf.neg.max measurable_const
  have hnpos (x : Point) : 0 ≤ fpos x := le_max_right _ _
  have hnneg (x : Point) : 0 ≤ fneg x := le_max_right _ _
  have hbpos := bounded_positivePart f hb
  have hbneg := bounded_positivePart (fun x => -f x) (by simpa only [abs_neg] using hb)
  have hsmallpos : bernoulli.real {x | fpos x ≠ 0} ≤ 1 / 2 := by
    rw [positivePart_support]
    apply measureReal_le_half
    simpa only [measure_univ] using hm.2
  have hsmallneg : bernoulli.real {x | fneg x ≠ 0} ≤ 1 / 2 := by
    rw [positivePart_support]
    have heq : {x | 0 < -f x} = {x | f x < 0} := by ext x; simp only [mem_setOf_eq, neg_pos]
    rw [heq]
    apply measureReal_le_half
    simpa only [measure_univ] using hm.1
  have hgpos := supported_integral_power_gap p hp fpos hfpos hnpos hbpos hsmallpos
  have hgneg := supported_integral_power_gap p hp fneg hfneg hnneg hbneg hsmallneg
  have hsplit (x : Point) : |f x| ^ p = fpos x ^ p + fneg x ^ p := by
    dsimp only [fpos, fneg]
    by_cases hx : 0 ≤ f x
    · simp [abs_of_nonneg hx, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx),
        Real.zero_rpow hp.ne']
    · have hx' : f x ≤ 0 := (lt_of_not_ge hx).le
      simp [abs_of_nonpos hx', max_eq_right hx', max_eq_left (neg_nonneg.mpr hx'),
        Real.zero_rpow hp.ne']
  have heq : (∫ x, |f x| ^ p ∂bernoulli) =
      (∫ x, fpos x ^ p ∂bernoulli) + ∫ x, fneg x ^ p ∂bernoulli := by
    simp_rw [hsplit]
    exact integral_add (bounded_power_integrable fpos hfpos hnpos hbpos p hp.le)
      (bounded_power_integrable fneg hfneg hnneg hbneg p hp.le)
  have hbound (g : Point → ℝ) (hg : ∀ x y, |g x - g y| ≤ |f x - f y|) (i : Fin 2) :
      (∫ x, |g (inverseGeneratorShift i x) - g x| ^ p ∂bernoulli) ≤
        ∫ x, |f (inverseGeneratorShift i x) - f x| ^ p ∂bernoulli := by
    apply integral_mono_of_nonneg (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg _) _)
      (bounded_difference_power_integrable f hf hb _ (continuous_shift _).measurable p hp.le)
    exact ae_of_all _ fun x => Real.rpow_le_rpow (abs_nonneg _) (hg _ _) hp.le
  have hpbound (i : Fin 2) := hbound fpos (fun x y => abs_max_sub_max_le_abs _ _ _) i
  have hnbound (i : Fin 2) :
      (∫ x, |fneg (inverseGeneratorShift i x) - fneg x| ^ p ∂bernoulli) ≤
        ∫ x, |f (inverseGeneratorShift i x) - f x| ^ p ∂bernoulli := by
    apply hbound fneg _ i
    intro x y
    simpa only [neg_sub_neg, abs_sub_comm] using abs_max_sub_max_le_abs (-f x) (-f y) 0
  have hK := powerGapConstant_nonneg hp
  rw [heq]
  have hpm := mul_le_mul_of_nonneg_left (add_le_add (hpbound 0) (hpbound 1)) hK
  have hnm := mul_le_mul_of_nonneg_left (add_le_add (hnbound 0) (hnbound 1)) hK
  linarith

theorem scalarPoincare_inverseGenerators (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    BenchmarkPoincareRadial.ScalarPoincareBound p bernoulli inverseGeneratorShift
      (ENNReal.ofReal (2 * powerGapConstant p.toReal)) := by
  intro f hf hm hb
  have hp0 : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
  have hg := median_integral_power_gap p.toReal hp0 f hf hm hb
  have hfi : Integrable (fun x => |f x| ^ p.toReal) bernoulli := by
    apply bounded_power_integrable _ hf.abs (fun x => abs_nonneg _) _ p.toReal hp0.le
    simpa only [abs_abs] using hb
  have hdi (i : Fin 2) := bounded_difference_power_integrable f hf hb (inverseGeneratorShift i)
    (continuous_shift (letterGroup (i, true))⁻¹).measurable p.toReal hp0.le
  have hleft := ofReal_integral_eq_lintegral_ofReal hfi
    (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg (f x)) p.toReal)
  have hright (i : Fin 2) := ofReal_integral_eq_lintegral_ofReal (hdi i)
    (ae_of_all _ fun x => Real.rpow_nonneg
      (abs_nonneg (f (inverseGeneratorShift i x) - f x)) p.toReal)
  have hnonneg (i : Fin 2) : 0 ≤
      ∫ x, |f (inverseGeneratorShift i x) - f x| ^ p.toReal ∂bernoulli :=
    integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
  have he := ENNReal.ofReal_le_ofReal hg
  rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) (powerGapConstant_nonneg hp0)),
    ENNReal.ofReal_add (hnonneg 0) (hnonneg 1), hleft, hright 0, hright 1] at he
  simpa only [BenchmarkRadialEnergy.scalarEnergy, Fin.sum_univ_two] using he

end BenchmarkShift
end
end Source30
end BenchmarkCountableProof

/- Whole source module: RealMedians -/
namespace BenchmarkCountableProof
section Source31
/-! Actual finite medians for real random variables, obtained from the
right-continuous cumulative distribution function. -/

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal

noncomputable section

namespace BenchmarkRealMedians

open BenchmarkPoincareRadial

theorem exists_real_distribution_median (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∃ m : ℝ, ν (Iio m) ≤ 1 / 2 ∧ ν (Ioi m) ≤ 1 / 2 := by
  let A : Set ℝ := {x | (1 / 2 : ℝ) ≤ cdf ν x}
  have hne : A.Nonempty := by
    obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop ν).eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).exists
    exact ⟨b, hb.le⟩
  have hbelow : BddBelow A := by
    obtain ⟨b, hb⟩ := ((tendsto_cdf_atBot ν).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
    refine ⟨b, fun a ha => ?_⟩
    by_contra hba
    have hlt : a < b := lt_of_not_ge hba
    have hmono := (monotone_cdf ν) hlt.le
    exact (not_lt_of_ge (ha.trans hmono)) hb
  let m := sInf A
  have hmright : (1 / 2 : ℝ) ≤ cdf ν m := by
    rw [← (cdf ν).iInf_Ioi_eq m]
    apply le_ciInf
    intro r
    obtain ⟨a, ha, har⟩ := (csInf_lt_iff hbelow hne).mp r.property
    exact ha.trans ((monotone_cdf ν) har.le)
  have hmleft : Function.leftLim (cdf ν) m ≤ (1 / 2 : ℝ) := by
    have hfilter : 𝓝[<] m ≠ ⊥ := by rw [← neBot_iff]; infer_instance
    rw [(monotone_cdf ν).leftLim_eq_sSup hfilter]
    apply csSup_le
    · exact ⟨cdf ν (m - 1), m - 1, by simp, rfl⟩
    · rintro z ⟨a, ha, rfl⟩
      have hnot : ¬ (1 / 2 : ℝ) ≤ cdf ν a := by
        intro haa
        have hma : m ≤ a := csInf_le hbelow haa
        exact not_le_of_gt ha hma
      exact (lt_of_not_ge hnot).le
  refine ⟨m, ?_, ?_⟩
  · have heq : ν (Iio m) = ENNReal.ofReal (Function.leftLim (cdf ν) m) := by
      calc
        ν (Iio m) = (cdf ν).measure (Iio m) := by rw [measure_cdf]
        _ = _ := by rw [(cdf ν).measure_Iio (tendsto_cdf_atBot ν), sub_zero]
    rw [heq]
    calc
      ENNReal.ofReal (leftLim (cdf ν) m) ≤ ENNReal.ofReal (1 / 2 : ℝ) := ENNReal.ofReal_le_ofReal hmleft
      _ = 1 / 2 := by norm_num [ENNReal.ofReal_div_of_pos]
  · have heq : ν (Ioi m) = ENNReal.ofReal (1 - cdf ν m) := by
      calc
        ν (Ioi m) = (cdf ν).measure (Ioi m) := by rw [measure_cdf]
        _ = _ := by rw [(cdf ν).measure_Ioi (tendsto_cdf_atTop ν)]
    rw [heq]
    calc
      ENNReal.ofReal (1 - cdf ν m) ≤ ENNReal.ofReal (1 / 2 : ℝ) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      _ = 1 / 2 := by norm_num [ENNReal.ofReal_div_of_pos]

theorem exists_zeroMedian {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (hf : Measurable f) :
    ∃ m : ℝ, ZeroMedian μ (fun x => f x - m) := by
  let ν := μ.map f
  haveI : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map hf.aemeasurable
  obtain ⟨m, hn, hp⟩ := exists_real_distribution_median ν
  refine ⟨m, ?_, ?_⟩
  · have heq : {x | f x - m < 0} = f ⁻¹' Iio m := by ext x; simp
    rw [heq, ← Measure.map_apply hf measurableSet_Iio]
    simpa only [measure_univ] using hn
  · have heq : {x | 0 < f x - m} = f ⁻¹' Ioi m := by ext x; simp
    rw [heq, ← Measure.map_apply hf measurableSet_Ioi]
    simpa only [measure_univ] using hp

theorem exists_coordinate_medians {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℕ → ℝ) (hf : Measurable f) :
    ∃ m : ℕ → ℝ, ∀ i, ZeroMedian μ (fun x => f x i - m i) := by
  have hex : ∀ i : ℕ, ∃ m : ℝ, ZeroMedian μ (fun x => f x i - m) :=
    fun i => exists_zeroMedian μ (fun x => f x i) ((measurable_pi_apply i).comp hf)
  exact Classical.axiom_of_choice hex

end BenchmarkRealMedians
end
end Source31
end BenchmarkCountableProof

/- Whole source module: TruncatedEnergy -/
namespace BenchmarkCountableProof
section Source32
/-!
# The nonintegrable truncated-energy step

The final limiting argument of the spectral-gap homomorphism theorem is
proved here without assuming integrability of any cocycle norm. The input
is the normalized truncated-energy inequality. Deriving that inequality
from scalar Poincaré inequalities and radial truncation is a separate
formalization obligation.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal

noncomputable section

namespace BenchmarkTruncatedEnergy

variable {X S : Type*} [MeasurableSpace X] [Fintype S]
  (μ : Measure X) [IsFiniteMeasure μ]

def realClip (c : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (min (c / ((n : ℝ) + 1)) 1)

def energyClip (H : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  min (H * ENNReal.ofReal (1 / ((n : ℝ) + 1))) 1

lemma realClip_le_one (c : ℝ) (n : ℕ) : realClip c n ≤ 1 := by
  exact (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans (by norm_num)

lemma realClip_tendsto_zero (c : ℝ) :
    Tendsto (fun n => realClip c n) atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ => c / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds (x := c)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [realClip, min_eq_left (by norm_num : (0 : ℝ) ≤ 1), ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal (hd.min (tendsto_const_nhds (x := (1 : ℝ))))

lemma energyClip_top (n : ℕ) : energyClip ∞ n = 1 := by
  have hp : 0 < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := ENNReal.ofReal_pos.mpr (by positivity)
  unfold energyClip
  rw [ENNReal.top_mul hp.ne']
  simp

lemma integral_realClip_tendsto_zero (c : X → ℝ) (hc : Measurable c) :
    Tendsto (fun n => ∫⁻ x, realClip (c x) n ∂μ) atTop (𝓝 0) := by
  have hm : ∀ n, Measurable (fun x => realClip (c x) n) := by
    intro n
    exact ((hc.div_const _).min measurable_const).ennreal_ofReal
  have hbound : ∀ n, (fun x => realClip (c x) n) ≤ᵐ[μ] fun _ => (1 : ℝ≥0∞) := by
    intro n
    exact ae_of_all μ (fun x => realClip_le_one (c x) n)
  have hfin : (∫⁻ _ : X, (1 : ℝ≥0∞) ∂μ) ≠ ∞ := by simp
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => realClip (c x) n) atTop (𝓝 0) :=
    ae_of_all μ fun x => realClip_tendsto_zero (c x)
  simpa only [lintegral_zero] using
    tendsto_lintegral_of_dominated_convergence (fun _ : X => (1 : ℝ≥0∞)) hm hbound hfin hlim

/-- Finite cocycle energies have vanishing normalized truncations. The
energies need only be measurable real-valued functions, not integrable. -/
theorem ae_finite_of_truncated_energy
    (H : X → ℝ≥0∞) (hH : Measurable H)
    (c : S → X → ℝ) (hc : ∀ s, Measurable (c s))
    (K : ℝ≥0∞) (hK : K ≠ ∞)
    (henergy : ∀ n : ℕ,
      (∫⁻ x, energyClip (H x) n ∂μ) ≤
        K * ∑ s : S, ∫⁻ x, realClip (c s x) n ∂μ) :
    ∀ᵐ x ∂μ, H x ≠ ∞ := by
  classical
  let A : Set X := {x | H x = ∞}
  have hA : MeasurableSet A := hH (measurableSet_singleton ∞)
  have hbound : ∀ n : ℕ, μ A ≤ K * ∑ s : S, ∫⁻ x, realClip (c s x) n ∂μ := by
    intro n
    apply le_trans _ (henergy n)
    calc
      μ A = ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by simp [hA]
      _ ≤ ∫⁻ x, energyClip (H x) n ∂μ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ A
        · rw [indicator_of_mem hx]
          have heq : H x = ∞ := hx
          change 1 ≤ energyClip (H x) n
          rw [heq, energyClip_top]
        · rw [indicator_of_notMem hx]
          exact bot_le
  have hsum : Tendsto (fun n => ∑ s : S, ∫⁻ x, realClip (c s x) n ∂μ)
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun s _ => integral_realClip_tendsto_zero μ (c s) (hc s))
  have hright : Tendsto (fun n => K * ∑ s : S, ∫⁻ x, realClip (c s x) n ∂μ)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hsum (Or.inr hK)
  have hzero : μ A = 0 := le_antisymm (ge_of_tendsto hright (Eventually.of_forall hbound)) bot_le
  rw [ae_iff]
  simpa only [not_not] using hzero

end BenchmarkTruncatedEnergy
end
end Source32
end BenchmarkCountableProof

/- Whole source module: PrefixTruncatedEnergy -/
namespace BenchmarkCountableProof
section Source33
/-! Both limiting steps in the spectral-gap energy argument: first let the
number of coordinates tend to infinity by monotone convergence, and then
let the truncation threshold tend to infinity. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

noncomputable section

namespace BenchmarkPrefixEnergy

open BenchmarkTruncatedEnergy

lemma energyClip_tsum (a : ℕ → ℝ≥0∞) (n : ℕ) :
    energyClip (∑' i, a i) n = ⨆ N : ℕ, energyClip (∑ i ∈ Finset.range N, a i) n := by
  unfold energyClip
  rw [ENNReal.tsum_eq_iSup_nat, ENNReal.iSup_mul]
  exact iSup_inf_eq _ _

variable {X S : Type*} [MeasurableSpace X] [Fintype S]
  (μ : Measure X) [IsFiniteMeasure μ]

theorem ae_finite_tsum_of_prefix_energy
    (a : ℕ → X → ℝ≥0∞) (ha : ∀ i, Measurable (a i))
    (c : S → X → ℝ) (hc : ∀ s, Measurable (c s))
    (K : ℝ≥0∞) (hK : K ≠ ∞)
    (henergy : ∀ N n : ℕ,
      (∫⁻ x, energyClip (∑ i ∈ Finset.range N, a i x) n ∂μ) ≤
        K * ∑ s : S, ∫⁻ x, realClip (c s x) n ∂μ) :
    ∀ᵐ x ∂μ, (∑' i, a i x) ≠ ∞ := by
  apply ae_finite_of_truncated_energy μ (fun x => ∑' i, a i x)
    (Measurable.ennreal_tsum ha) c hc K hK
  intro n
  have hm : ∀ N : ℕ, Measurable (fun x => energyClip (∑ i ∈ Finset.range N, a i x) n) := by
    intro N
    unfold energyClip
    exact ((Finset.measurable_sum _ (fun i _ => ha i)).mul_const _).min measurable_const
  have hmono : Monotone (fun N : ℕ => fun x => energyClip (∑ i ∈ Finset.range N, a i x) n) := by
    intro N M hNM x
    unfold energyClip
    apply min_le_min_right
    apply mul_le_mul_right'
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hNM)
  calc
    (∫⁻ x, energyClip (∑' i, a i x) n ∂μ) =
        ∫⁻ x, ⨆ N : ℕ, energyClip (∑ i ∈ Finset.range N, a i x) n ∂μ := by
      congr 1
      funext x
      exact energyClip_tsum (fun i => a i x) n
    _ = ⨆ N : ℕ, ∫⁻ x, energyClip (∑ i ∈ Finset.range N, a i x) n ∂μ := lintegral_iSup hm hmono
    _ ≤ K * ∑ s : S, ∫⁻ x, realClip (c s x) n ∂μ := iSup_le fun N => henergy N n

theorem ae_summable_of_prefix_energy
    (a : ℕ → X → ℝ) (ha : ∀ i, Measurable (a i)) (ha0 : ∀ i x, 0 ≤ a i x)
    (c : S → X → ℝ) (hc : ∀ s, Measurable (c s))
    (K : ℝ≥0∞) (hK : K ≠ ∞)
    (henergy : ∀ N n : ℕ,
      (∫⁻ x, energyClip (∑ i ∈ Finset.range N, ENNReal.ofReal (a i x)) n ∂μ) ≤
        K * ∑ s : S, ∫⁻ x, realClip (c s x) n ∂μ) :
    ∀ᵐ x ∂μ, Summable (fun i => a i x) := by
  have hf := ae_finite_tsum_of_prefix_energy μ (fun i x => ENNReal.ofReal (a i x))
    (fun i => (ha i).ennreal_ofReal) c hc K hK henergy
  filter_upwards [hf] with x hx
  have hs := ENNReal.summable_toReal hx
  simpa only [ENNReal.toReal_ofReal (ha0 _ x)] using hs

end BenchmarkPrefixEnergy
end
end Source33
end BenchmarkCountableProof

/- Whole source module: NormalizedTruncation -/
namespace BenchmarkCountableProof
section Source34
/-! Normalization of the finite-prefix energy estimates. Displacement
energies are only assumed finite almost everywhere, with no integrability
requirement. This closes the two-limit argument for such estimates. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

noncomputable section

namespace BenchmarkNormalizedTruncation

open BenchmarkTruncatedEnergy BenchmarkPrefixEnergy

def threshold (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((n : ℝ) + 1)
def reciprocal (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1 / ((n : ℝ) + 1))

lemma reciprocal_mul_threshold (n : ℕ) : reciprocal n * threshold n = 1 := by
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  unfold reciprocal threshold
  rw [← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hpos.ne']
  norm_num

lemma energyClip_eq_scaled_min (H : ℝ≥0∞) (n : ℕ) :
    energyClip H n = reciprocal n * min H (threshold n) := by
  unfold energyClip
  rw [mul_min, reciprocal_mul_threshold, mul_comm (reciprocal n) H]
  rfl

lemma realClip_toReal (c : ℝ≥0∞) (hc : c ≠ ∞) (n : ℕ) :
    realClip c.toReal n = energyClip c n := by
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  unfold realClip energyClip
  rw [ENNReal.ofReal_min, ENNReal.ofReal_one, ENNReal.ofReal_div_of_pos hpos,
    ENNReal.ofReal_toReal hc, div_eq_mul_inv, one_div, ENNReal.ofReal_inv_of_pos hpos]

variable {X S : Type*} [MeasurableSpace X] [Fintype S]
  (μ : Measure X) [IsFiniteMeasure μ]

lemma integral_energyClip (H : X → ℝ≥0∞) (n : ℕ) :
    (∫⁻ x, energyClip (H x) n ∂μ) =
      reciprocal n * ∫⁻ x, min (H x) (threshold n) ∂μ := by
  simp_rw [energyClip_eq_scaled_min]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Finite-prefix unnormalized truncated-energy inequalities force almost
every full energy sum to be finite. The comparison energies may be
unbounded and need not belong to L¹. -/
theorem ae_finite_tsum_of_unnormalized_energy
    (a : ℕ → X → ℝ≥0∞) (ha : ∀ i, Measurable (a i))
    (c : S → X → ℝ≥0∞) (hc : ∀ s, Measurable (c s))
    (hcfinite : ∀ s, ∀ᵐ x ∂μ, c s x ≠ ∞)
    (K : ℝ≥0∞) (hK : K ≠ ∞)
    (henergy : ∀ N n : ℕ,
      (∫⁻ x, min (∑ i ∈ Finset.range N, a i x) (threshold n) ∂μ) ≤
        K * ∑ s : S, ∫⁻ x, min (c s x) (threshold n) ∂μ) :
    ∀ᵐ x ∂μ, (∑' i, a i x) ≠ ∞ := by
  classical
  apply ae_finite_tsum_of_prefix_energy μ a ha (fun s x => (c s x).toReal)
    (fun s => (hc s).ennreal_toReal) K hK
  intro N n
  have hrewrite : (∑ s : S, ∫⁻ x, energyClip (c s x) n ∂μ) =
      ∑ s : S, ∫⁻ x, realClip (c s x).toReal n ∂μ := by
    apply Finset.sum_congr rfl
    intro s _
    apply lintegral_congr_ae
    filter_upwards [hcfinite s] with x hx
    exact (realClip_toReal (c s x) hx n).symm
  calc
    (∫⁻ x, energyClip (∑ i ∈ Finset.range N, a i x) n ∂μ) =
        reciprocal n * ∫⁻ x, min (∑ i ∈ Finset.range N, a i x) (threshold n) ∂μ :=
      integral_energyClip μ _ n
    _ ≤ reciprocal n * (K * ∑ s : S, ∫⁻ x, min (c s x) (threshold n) ∂μ) :=
      mul_le_mul_left' (henergy N n) _
    _ = K * ∑ s : S, ∫⁻ x, energyClip (c s x) n ∂μ := by
      simp_rw [integral_energyClip μ]
      rw [← Finset.mul_sum]
      ac_rfl
    _ = K * ∑ s : S, ∫⁻ x, realClip (c s x).toReal n ∂μ := by rw [hrewrite]

end BenchmarkNormalizedTruncation
end
end Source34
end BenchmarkCountableProof

/- Whole source module: SequencePoincareCollapse -/
namespace BenchmarkCountableProof
section Source35
/-!
# Sequence-valued homomorphism collapse from scalar Poincaré bounds

The supplied medians and scalar Poincaré bound imply almost-everywhere
ℓp-equivalence to their median sequence. Displacement sequences need only
be summable almost everywhere; their norms need not be integrable.

This proves the analytic implication used in the manuscript. Existence
of real medians and the scalar Poincaré bound for the Bernoulli action are
separate inputs, not claimed here as already formalized theorems.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

noncomputable section

namespace BenchmarkSequencePoincare

open BenchmarkPoincareRadial BenchmarkRadialEnergy BenchmarkNormalizedTruncation

variable {X S : Type*} [MeasurableSpace X] [Fintype S]
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure X) [IsFiniteMeasure μ]

def prefixVector (f : X → ℕ → ℝ) (m : ℕ → ℝ) (N : ℕ) (x : X) : Vector (I := Fin N) p :=
  WithLp.toLp p (fun i : Fin N => f x i - m i)

lemma measurable_prefixVector (f : X → ℕ → ℝ) (hf : Measurable f) (m : ℕ → ℝ) (N : ℕ) :
    Measurable (prefixVector p f m N) := by
  apply (WithLp.measurable_toLp p _).comp
  exact measurable_pi_lambda _ (fun i => ((measurable_pi_apply (i : ℕ)).comp hf).sub_const _)

lemma prefixVector_energy (hp : p ≠ ∞) (f : X → ℕ → ℝ) (m : ℕ → ℝ) (N : ℕ) (x : X) :
    vectorEnergy p (prefixVector p f m N x) =
      ∑ i ∈ Finset.range N, ENNReal.ofReal (|f x i - m i| ^ p.toReal) := by
  rw [vectorEnergy_eq_sum p hp, Finset.sum_range]
  rfl

theorem ae_summable_centered_of_poincare
    (hp : p ≠ ∞) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (t : S → X → X) (ht : ∀ s, Measurable (t s))
    (hP : ScalarPoincareBound p μ t C)
    (f : X → ℕ → ℝ) (hf : Measurable f) (m : ℕ → ℝ)
    (hm : ∀ i, ZeroMedian μ (fun x => f x i - m i))
    (hdisplacement : ∀ s, ∀ᵐ x ∂μ,
      Summable (fun i => |f (t s x) i - f x i| ^ p.toReal)) :
    ∀ᵐ x ∂μ, Summable (fun i => |f x i - m i| ^ p.toReal) := by
  classical
  let a := fun i x => ENNReal.ofReal (|f x i - m i| ^ p.toReal)
  let c := fun s x => ∑' i, ENNReal.ofReal (|f (t s x) i - f x i| ^ p.toReal)
  let K := ENNReal.ofReal ((2 : ℝ) ^ p.toReal) * C
  have ha : ∀ i, Measurable (a i) := by
    intro i
    exact (((((measurable_pi_apply i).comp hf).sub_const _).abs).pow_const _).ennreal_ofReal
  have hc : ∀ s, Measurable (c s) := by
    intro s
    apply Measurable.ennreal_tsum
    intro i
    exact (((((measurable_pi_apply i).comp (hf.comp (ht s))).sub
      ((measurable_pi_apply i).comp hf)).abs).pow_const _).ennreal_ofReal
  have hcf : ∀ s, ∀ᵐ x ∂μ, c s x ≠ ∞ := by
    intro s
    filter_upwards [hdisplacement s] with x hx
    exact hx.tsum_ofReal_ne_top
  have hK : K ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC
  have hfinite : ∀ᵐ x ∂μ, (∑' i, a i x) ≠ ∞ := by
    apply ae_finite_tsum_of_unnormalized_energy μ a ha c hc hcf K hK
    intro N n
    let R := ((n : ℝ) + 1) ^ (1 / p.toReal)
    have hR : 0 < R := Real.rpow_pos_of_pos (by positivity) _
    have hq : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
    have hRq : R ^ p.toReal = (n : ℝ) + 1 := by
      dsimp [R]
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hq.ne', Real.rpow_one]
    let v := prefixVector p f m N
    have hv := measurable_prefixVector p f hf m N
    have hmed : ∀ i : Fin N, ZeroMedian μ (fun x => v x i) := fun i => hm i
    have htrunc := truncated_energy_of_poincare p μ hp hR C t ht hP v hv hmed
    have hleft : ∀ x, ENNReal.ofReal (min (‖v x‖ ^ p.toReal) (R ^ p.toReal)) =
        min (∑ i ∈ Finset.range N, a i x) (threshold n) := by
      intro x
      rw [ENNReal.ofReal_min, hRq]
      change min (vectorEnergy p (v x)) (threshold n) = _
      rw [prefixVector_energy p hp f m N x]
    have hnorm : ∀ s x, vectorEnergy p (v (t s x) - v x) ≤ c s x := by
      intro s x
      rw [vectorEnergy_eq_sum p hp]
      have hb := ENNReal.sum_le_tsum (Finset.range N)
        (f := fun i => ENNReal.ofReal (|f (t s x) i - f x i| ^ p.toReal))
      rw [Finset.sum_range] at hb
      simpa only [scalarEnergy, v, prefixVector, PiLp.sub_apply, PiLp.toLp_apply,
        sub_sub_sub_cancel_right] using hb
    have hr : ∀ s,
        (∫⁻ x, ENNReal.ofReal (min (‖v (t s x) - v x‖ ^ p.toReal) (R ^ p.toReal)) ∂μ) ≤
          ∫⁻ x, min (c s x) (threshold n) ∂μ := by
      intro s
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (min (‖v (t s x) - v x‖ ^ p.toReal) (R ^ p.toReal)) ≤
        min (c s x) (threshold n)
      rw [ENNReal.ofReal_min, hRq]
      exact min_le_min_right _ (hnorm s x)
    have hfirst : (∫⁻ x, min (∑ i ∈ Finset.range N, a i x) (threshold n) ∂μ) ≤
        K * ∑ s : S, ∫⁻ x, ENNReal.ofReal (min (‖v (t s x) - v x‖ ^ p.toReal) (R ^ p.toReal)) ∂μ := by
      simpa only [hleft, K, mul_assoc] using htrunc
    exact hfirst.trans (mul_le_mul_left' (Finset.sum_le_sum fun s _ => hr s) K)
  filter_upwards [hfinite] with x hx
  have hs := ENNReal.summable_toReal hx
  simpa only [a, ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg _) _)] using hs

end BenchmarkSequencePoincare
end
end Source35
end BenchmarkCountableProof

/- Whole source module: PoincareNonreduction -/
namespace BenchmarkCountableProof
section Source36
/-! The measure-theoretic contradiction after scalar Poincaré collapse.
The abstract criterion below still requires a Poincaré bound for the chosen
source transformations; it does not assert that the Bernoulli bound has
already been formalized. -/

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace BenchmarkPoincareNonreduction

open BenchmarkPoincareRadial BenchmarkSequencePoincare BenchmarkRealMedians

lemma summable_difference_of_common_center
    (p : ℝ≥0∞) (hp : 0 < p.toReal) (a b m : ℕ → ℝ)
    (ha : Summable (fun i => |a i - m i| ^ p.toReal))
    (hb : Summable (fun i => |b i - m i| ^ p.toReal)) :
    Summable (fun i => |a i - b i| ^ p.toReal) := by
  have hma : Memℓp (fun i => a i - m i) p :=
    (memℓp_gen_iff hp).mpr (by simpa only [Real.norm_eq_abs] using ha)
  have hmb : Memℓp (fun i => b i - m i) p :=
    (memℓp_gen_iff hp).mpr (by simpa only [Real.norm_eq_abs] using hb)
  have hsub := (memℓp_gen_iff hp).mp (hma.sub hmb)
  simpa only [Pi.sub_apply, Real.norm_eq_abs, sub_sub_sub_cancel_right] using hsub

theorem exists_almost_sure_lp_class
    {X S : Type*} [MeasurableSpace X] [Fintype S]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (C : ℝ≥0∞) (hC : C ≠ ∞) (t : S → X → X) (ht : ∀ s, Measurable (t s))
    (hP : ScalarPoincareBound p μ t C)
    (f : X → ℕ → ℝ) (hf : Measurable f)
    (hdisplacement : ∀ s, ∀ᵐ x ∂μ,
      Summable (fun i => |f (t s x) i - f x i| ^ p.toReal)) :
    ∃ m : ℕ → ℝ, ∀ᵐ x ∂μ, Summable (fun i => |f x i - m i| ^ p.toReal) := by
  obtain ⟨m, hm⟩ := exists_coordinate_medians μ f hf
  exact ⟨m, ae_summable_centered_of_poincare p μ hp C hC t ht hP f hf m hm hdisplacement⟩

theorem no_lp_reduction_of_null_classes_and_poincare
    {X S : Type*} [MeasurableSpace X] [Fintype S]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (μ : Measure X) [IsProbabilityMeasure μ] (E : X → X → Prop)
    (hnull : ∀ x, μ {y | E x y} = 0)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (t : S → X → X) (ht : ∀ s, Measurable (t s))
    (hE : ∀ s, ∀ᵐ x ∂μ, E (t s x) x)
    (hP : ScalarPoincareBound p μ t C) :
    ¬ ∃ f : X → ℕ → ℝ, Measurable f ∧
      ∀ x y, E x y ↔ Summable (fun i => |f x i - f y i| ^ p.toReal) := by
  rintro ⟨f, hf, hred⟩
  have hdisplacement : ∀ s, ∀ᵐ x ∂μ,
      Summable (fun i => |f (t s x) i - f x i| ^ p.toReal) := by
    intro s
    filter_upwards [hE s] with x hx
    exact (hred (t s x) x).mp hx
  obtain ⟨m, hm⟩ := exists_almost_sure_lp_class p hp μ C hC t ht hP f hf hdisplacement
  obtain ⟨x₀, hx₀⟩ := hm.exists
  have hclass : ∀ᵐ x ∂μ, E x₀ x := by
    filter_upwards [hm] with x hx
    exact (hred x₀ x).mpr
      (summable_difference_of_common_center p (p.toReal_pos_iff_ne_top.mpr hp) _ _ _ hx₀ hx)
  let A : Set X := {x | E x₀ x}
  have hAzero : μ A = 0 := hnull x₀
  have hAc : μ Aᶜ = 0 := by simpa only [A, compl_setOf] using ae_iff.mp hclass
  have huniv : μ univ = 0 := by
    apply le_antisymm _ bot_le
    calc
      μ univ = μ (A ∪ Aᶜ) := by rw [union_compl_self]
      _ ≤ μ A + μ Aᶜ := measure_union_le _ _
      _ = 0 := by rw [hAzero, hAc, zero_add]
  exact (one_ne_zero : (1 : ℝ≥0∞) ≠ 0) (by simpa only [measure_univ] using huniv)

end BenchmarkPoincareNonreduction
end
end Source36
end BenchmarkCountableProof

/- Whole source module: ShiftFiniteLpObstruction -/
namespace BenchmarkCountableProof
section Source37
/-! The unconditional finite-ℓp obstruction for the actual full free-group shift.
The scalar Poincaré inequality, atomlessness, and nullity of every orbit are
proved in the imported modules; this theorem has no classification hypothesis. -/

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkShift

theorem eInfinity_not_reduces_ENNlp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ¬ BenchmarkComparisons.BorelReduces BenchmarkComparisons.EInfinity
      (BenchmarkComparisons.LpDifference p.toReal) := by
  apply BenchmarkPoincareNonreduction.no_lp_reduction_of_null_classes_and_poincare
    p hp bernoulli Orbit bernoulli_orbit_zero
    (ENNReal.ofReal (2 * powerGapConstant p.toReal)) ENNReal.ofReal_ne_top inverseGeneratorShift
  · intro i
    exact (continuous_shift (letterGroup (i, true))⁻¹).measurable
  · intro i
    apply ae_of_all
    intro x
    exact (orbit_iff_reachable _ _).mpr
      (reachable_shift (letterGroup (i, true))⁻¹ x).symm
  · exact scalarPoincare_inverseGenerators p hp

theorem eInfinity_not_reduces_finiteLp (p : ℝ) (hp : 1 ≤ p) :
    ¬ BenchmarkComparisons.BorelReduces BenchmarkComparisons.EInfinity
      (BenchmarkComparisons.LpDifference p) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  have h := eInfinity_not_reduces_ENNlp (ENNReal.ofReal p) ENNReal.ofReal_ne_top
  simpa only [ENNReal.toReal_ofReal (le_trans zero_le_one hp)] using h

end BenchmarkShift
end
end Source37
end BenchmarkCountableProof

/- Whole source module: JumpRows -/
namespace BenchmarkCountableProof
section Source38
/-! The common category lemma used in both jump-obstruction proofs of
`Benchmark.tex`.  This file proves the category and row-support argument.
It does not assert either of the two obstruction theorems: obtaining the
local row hypothesis for their two concrete source spaces is separate work. -/

open Filter Set Topology TopologicalSpace
open scoped Topology

namespace BenchmarkJump

variable {X Y : Type*}

/-- The Friedman--Stanley jump records precisely the countable set of row classes. -/
def Jump (R : Y → Y → Prop) (u v : ℕ → Y) : Prop :=
  (∀ k, ∃ l, R (u k) (v l)) ∧ (∀ l, ∃ k, R (u k) (v l))

def Homomorphism (E : X → X → Prop) (R : Y → Y → Prop) (F : X → Y) : Prop :=
  ∀ x y, E x y → R (F x) (F y)

variable [TopologicalSpace X]

/-- Generic ergodicity, stated for invariant sets with the Baire property. -/
def GenericallyErgodic (E : X → X → Prop) : Prop :=
  ∀ s : Set X, BaireMeasurableSet s →
    (∀ x y, E x y → (x ∈ s ↔ y ∈ s)) →
    IsMeagre s ∨ s ∈ residual X

/-- Local constancy is comeagerness relative to the open set, expressed as
an eventual implication in the ambient residual filter. -/
def LocallyGenericallyConstantRows (R : Y → Y → Prop)
    (F : X → ℕ → Y) : Prop :=
  ∀ k (A : Set X), IsOpen A → A.Nonempty →
    ∃ O : Set X, ∃ a : Y, IsOpen O ∧ O.Nonempty ∧ O ⊆ A ∧
      ∀ᶠ x in residual X, x ∈ O → R (F x k) a

/-- A countable basis turns the local row hypothesis into a single countable
family containing all row classes at comeager many source points. -/
theorem countable_row_representatives [SecondCountableTopology X]
    (R : Y → Y → Prop) (F : X → ℕ → Y)
    (hloc : LocallyGenericallyConstantRows R F) :
    ∃ a : ℕ × countableBasis X → Y,
      ∀ᶠ x in residual X, ∀ k, ∃ r, R (F x k) (a r) := by
  classical
  choose O a hOo hOn hOs hOres using fun (k : ℕ) (B : countableBasis X) =>
    hloc k B (isOpen_of_mem_countableBasis B.property)
      (nonempty_of_mem_countableBasis B.property)
  have hDense (k : ℕ) : Dense (⋃ B, O k B) := by
    apply dense_iff_inter_open.2
    intro U hU hUn
    obtain ⟨x, hx⟩ := hUn
    obtain ⟨B, hB, _hxB, hBU⟩ :=
      (isBasis_countableBasis X).exists_subset_of_mem_open hx hU
    obtain ⟨y, hy⟩ := hOn k ⟨B, hB⟩
    exact ⟨y, hBU (hOs k ⟨B, hB⟩ hy), mem_iUnion.2 ⟨⟨B, hB⟩, hy⟩⟩
  have hCover : ∀ᶠ x in residual X, ∀ k, x ∈ ⋃ B, O k B :=
    eventually_countable_forall.2 fun k =>
      residual_of_dense_open (isOpen_iUnion (hOo k)) (hDense k)
  have hGood : ∀ᶠ x in residual X, ∀ r : ℕ × countableBasis X,
      x ∈ O r.1 r.2 → R (F x r.1) (a r.1 r.2) :=
    eventually_countable_forall.2 fun r => hOres r.1 r.2
  refine ⟨fun r => a r.1 r.2, ?_⟩
  filter_upwards [hCover, hGood] with x hx hg
  intro k
  obtain ⟨B, hB⟩ := mem_iUnion.1 (hx k)
  exact ⟨(k, B), hg (k, B) hB⟩

/-- Jump homomorphisms preserve the membership of every fixed target class
in their countable set of row classes. -/
theorem row_support_invariant (R : Y → Y → Prop) (hR : Equivalence R)
    (E : X → X → Prop) (F : X → ℕ → Y)
    (hF : Homomorphism E (Jump R) F) (a : Y) :
    ∀ x y, E x y →
      ((∃ k, R (F x k) a) ↔ ∃ k, R (F y k) a) := by
  intro x y hxy
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨l, hl⟩ := (hF x y hxy).1 k
    exact ⟨l, hR.trans (hR.symm hl) hk⟩
  · rintro ⟨l, hl⟩
    obtain ⟨k, hk⟩ := (hF x y hxy).2 l
    exact ⟨k, hR.trans hk hl⟩

/-- Countably many Baire invariant coordinates are simultaneously constant
on one comeager set. -/
theorem invariant_coordinates_constant {ι : Type*} [Countable ι]
    (E : X → X → Prop) (hE : GenericallyErgodic E)
    (P : ι → X → Prop)
    (hP : ∀ i, BaireMeasurableSet {x | P i x})
    (hInv : ∀ i x y, E x y → (P i x ↔ P i y)) :
    ∃ b : ι → Bool, ∀ᶠ x in residual X, ∀ i, P i x ↔ b i = true := by
  classical
  have hOne (i : ι) : ∃ b : Bool,
      ∀ᶠ x in residual X, P i x ↔ b = true := by
    rcases hE {x | P i x} (hP i) (hInv i) with hm | hr
    · refine ⟨false, ?_⟩
      filter_upwards [hm] with x hx
      simp only [mem_compl_iff, mem_setOf_eq] at hx
      simp [hx]
    · refine ⟨true, ?_⟩
      filter_upwards [hr] with x hx
      simpa using hx
  choose b hb using hOne
  exact ⟨b, eventually_countable_forall.2 hb⟩

/-- The countable-class part of the row lemma, after the countable basis
argument has produced representatives. -/
theorem generically_constant_of_representatives {ι : Type*} [Countable ι]
    [Nonempty X] [BaireSpace X]
    (E : X → X → Prop) (R : Y → Y → Prop) (hR : Equivalence R)
    (F : X → ℕ → Y) (hF : Homomorphism E (Jump R) F)
    (hE : GenericallyErgodic E) (a : ι → Y)
    (hRep : ∀ᶠ x in residual X, ∀ k, ∃ r, R (F x k) (a r))
    (hBaire : ∀ r, BaireMeasurableSet {x | ∃ k, R (F x k) (a r)}) :
    ∃ v : ℕ → Y, ∀ᶠ x in residual X, Jump R (F x) v := by
  obtain ⟨b, hb⟩ := invariant_coordinates_constant E hE
    (fun r x => ∃ k, R (F x k) (a r)) hBaire
    (fun r => row_support_invariant R hR E F hF (a r))
  obtain ⟨x₀, hxRep, hxBool⟩ := (dense_of_mem_residual (hRep.and hb)).nonempty
  refine ⟨F x₀, ?_⟩
  filter_upwards [hRep, hb] with x hxR hxb
  constructor
  · intro k
    obtain ⟨r, hr⟩ := hxR k
    have hrb : b r = true := (hxb r).mp ⟨k, hr⟩
    obtain ⟨l, hl⟩ := (hxBool r).mpr hrb
    exact ⟨l, hR.trans hr (hR.symm hl)⟩
  · intro l
    obtain ⟨r, hr⟩ := hxRep l
    have hrb : b r = true := (hxBool r).mp ⟨l, hr⟩
    obtain ⟨k, hk⟩ := (hxb r).mpr hrb
    exact ⟨k, hR.trans hk (hR.symm hr)⟩

/-- Borel row maps and a Borel target relation give Baire measurable
class-support coordinates, as required by generic ergodicity. -/
theorem row_support_baire [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    (R : Y → Y → Prop) (hR : MeasurableSet {p : Y × Y | R p.1 p.2})
    (F : X → ℕ → Y) (hF : Measurable F) (a : Y) :
    BaireMeasurableSet {x | ∃ k, R (F x k) a} := by
  apply MeasurableSet.baireMeasurableSet
  have hOne (k : ℕ) : MeasurableSet {x | R (F x k) a} :=
    hR.preimage (((measurable_pi_apply k).comp hF).prodMk measurable_const)
  simpa only [setOf_exists] using MeasurableSet.iUnion hOne

/-- Lemma `rows` of the manuscript, with its Borel and topology assumptions
made explicit. This proves the common row-to-jump category implication in full. -/
theorem locally_constant_rows_imp_constant_jump
    [SecondCountableTopology X] [Nonempty X] [BaireSpace X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    (E : X → X → Prop) (R : Y → Y → Prop) (hR : Equivalence R)
    (hRBorel : MeasurableSet {p : Y × Y | R p.1 p.2})
    (F : X → ℕ → Y) (hFmeas : Measurable F)
    (hF : Homomorphism E (Jump R) F) (hE : GenericallyErgodic E)
    (hloc : LocallyGenericallyConstantRows R F) :
    ∃ v : ℕ → Y, ∀ᶠ x in residual X, Jump R (F x) v := by
  obtain ⟨a, ha⟩ := countable_row_representatives R F hloc
  exact generically_constant_of_representatives E R hR F hF hE a ha
    (fun r => row_support_baire R hRBorel F hFmeas (a r))

theorem jump_equivalence (R : Y → Y → Prop) (hR : Equivalence R) :
    Equivalence (Jump R) := by
  constructor
  · intro x
    exact ⟨fun k => ⟨k, hR.refl _⟩, fun k => ⟨k, hR.refl _⟩⟩
  · intro x y hxy
    exact ⟨fun k => (hxy.2 k).imp fun l hl => hR.symm hl,
      fun l => (hxy.1 l).imp fun k hk => hR.symm hk⟩
  · intro x y z hxy hyz
    constructor
    · intro k
      obtain ⟨l, hl⟩ := hxy.1 k
      obtain ⟨m, hm⟩ := hyz.1 l
      exact ⟨m, hR.trans hl hm⟩
    · intro m
      obtain ⟨l, hl⟩ := hyz.2 m
      obtain ⟨k, hk⟩ := hxy.2 l
      exact ⟨k, hR.trans hk hl⟩

/-- A relation with meager classes cannot have a reduction that is constant
modulo the target on a comeager set. No descriptive-set-theoretic obstruction
is assumed in this implication. -/
theorem not_reduction_of_generic_constancy [Nonempty X] [BaireSpace X]
    (E : X → X → Prop) (R : Y → Y → Prop) (hR : Equivalence R)
    (hClasses : ∀ x, IsMeagre {y | E y x})
    (F : X → Y) (hConst : ∃ v, ∀ᶠ x in residual X, R (F x) v) :
    ¬ (∀ x y, E x y ↔ R (F x) (F y)) := by
  intro hRed
  obtain ⟨v, hv⟩ := hConst
  obtain ⟨x₀, hx₀⟩ := (dense_of_mem_residual hv).nonempty
  have hClass : {y | R (F y) v} ⊆ {y | E y x₀} := by
    intro y hy
    exact (hRed y x₀).mpr (hR.trans hy (hR.symm hx₀))
  exact not_isMeagre_of_mem_residual hv ((hClasses x₀).mono hClass)

/-- The general reduction obstruction after local row constancy and
generic ergodicity have been proved for a concrete source. -/
theorem not_borel_reduction_of_local_rows
    [SecondCountableTopology X] [Nonempty X] [BaireSpace X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    (E : X → X → Prop) (R : Y → Y → Prop) (hR : Equivalence R)
    (hRBorel : MeasurableSet {p : Y × Y | R p.1 p.2})
    (hE : GenericallyErgodic E) (hClasses : ∀ x, IsMeagre {y | E y x})
    (hLocal : ∀ F : X → ℕ → Y, Measurable F →
      Homomorphism E (Jump R) F → LocallyGenericallyConstantRows R F) :
    ¬ ∃ F : X → ℕ → Y, Measurable F ∧
      ∀ x y, E x y ↔ Jump R (F x) (F y) := by
  rintro ⟨F, hFm, hRed⟩
  have hF : Homomorphism E (Jump R) F := fun x y h => (hRed x y).mp h
  have hConst := locally_constant_rows_imp_constant_jump E R hR hRBorel F hFm hF hE
    (hLocal F hFm hF)
  exact not_reduction_of_generic_constancy E (Jump R) (jump_equivalence R hR)
    hClasses F hConst hRed




end BenchmarkJump
end Source38
end BenchmarkCountableProof

/- Whole source module: CategoryTools -/
namespace BenchmarkCountableProof
section Source39
/-! Category tools needed by the concrete jump-obstruction arguments. -/

open Filter Set Topology TopologicalSpace
open scoped Topology

namespace BenchmarkJump

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A Borel map into a second-countable space is continuous on a dense
Gdelta subspace of any Baire domain. This is relative continuity. -/
theorem measurable_continuousOn_residual
    [BaireSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    (f : X → Y) (hf : Measurable f) :
    ∃ D : Set X, IsGδ D ∧ Dense D ∧ ContinuousOn f D := by
  classical
  have hB (B : countableBasis Y) :
      BaireMeasurableSet (f ⁻¹' (B : Set Y)) :=
    (hf (isOpen_of_mem_countableBasis B.property).measurableSet).baireMeasurableSet
  choose U hU hEq using fun B : countableBasis Y => (hB B).residualEq_isOpen
  have hAll : ∀ᶠ x in residual X, ∀ B : countableBasis Y,
      f x ∈ (B : Set Y) ↔ x ∈ U B :=
    eventually_countable_forall.2 fun B => Filter.eventuallyEq_set.mp (hEq B)
  obtain ⟨D, hDG, hDd, hD⟩ := eventually_residual.mp hAll
  refine ⟨D, hDG, hDd, (isBasis_countableBasis Y).continuousOn_iff.mpr ?_⟩
  intro B hB
  refine ⟨U ⟨B, hB⟩, hU _, ?_⟩
  ext x
  constructor
  · rintro ⟨hxB, hxD⟩
    exact ⟨(hD x hxD ⟨B, hB⟩).mp hxB, hxD⟩
  · rintro ⟨hxU, hxD⟩
    exact ⟨(hD x hxD ⟨B, hB⟩).mpr hxU, hxD⟩

/-- The projection of an open relation intersected with a nonempty open
vertical set is open. -/
theorem isOpen_exists_vertical {U : Set (X × Y)} (hU : IsOpen U)
    {V : Set Y} (hV : IsOpen V) :
    IsOpen {x | ∃ y ∈ V, (x, y) ∈ U} := by
  have heq : {x | ∃ y ∈ V, (x, y) ∈ U} =
      Prod.fst '' (U ∩ Prod.snd ⁻¹' V) := by
    ext x
    constructor
    · rintro ⟨y, hyV, hxy⟩
      exact ⟨(x, y), ⟨hxy, hyV⟩, rfl⟩
    · rintro ⟨⟨x', y⟩, ⟨hxy, hyV⟩, hxx⟩
      change x' = x at hxx
      subst x'
      exact ⟨y, hyV, hxy⟩
  rw [heq]
  exact isOpenMap_fst _ (hU.inter (hV.preimage continuous_snd))

/-- The same projection is dense when the relation is open dense and the
vertical set is nonempty open. -/
theorem dense_exists_vertical {U : Set (X × Y)} (hUd : Dense U)
    {V : Set Y} (hVo : IsOpen V) (hVn : V.Nonempty) :
    Dense {x | ∃ y ∈ V, (x, y) ∈ U} := by
  apply dense_iff_inter_open.mpr
  intro A hAo hAn
  obtain ⟨x, hx⟩ := hAn
  obtain ⟨y, hy⟩ := hVn
  obtain ⟨⟨x', y'⟩, ⟨hxA, hyV⟩, hxyU⟩ :=
    hUd.inter_open_nonempty (A ×ˢ V) (hAo.prod hVo) ⟨(x, y), hx, hy⟩
  exact ⟨x', hxA, y', hyV, hxyU⟩

/-- The residual-set direction of Kuratowski--Ulam, proved from countable
bases and dense open projections. This suffices for the manuscript's use. -/
theorem eventually_residual_prod [SecondCountableTopology Y]
    {P : X × Y → Prop} (hP : ∀ᶠ p in residual (X × Y), P p) :
    ∀ᶠ x in residual X, ∀ᶠ y in residual Y, P (x, y) := by
  classical
  obtain ⟨S, hSo, hSd, hSc, hS⟩ := mem_residual_iff.mp hP
  letI : Countable S := hSc.to_subtype
  have hAll : ∀ᶠ x in residual X, ∀ U : S, ∀ B : countableBasis Y,
      ∃ y ∈ (B : Set Y), (x, y) ∈ (U : Set (X × Y)) := by
    apply eventually_countable_forall.mpr
    intro U
    apply eventually_countable_forall.mpr
    intro B
    exact residual_of_dense_open
      (isOpen_exists_vertical (hSo U U.property)
        (isOpen_of_mem_countableBasis B.property))
      (dense_exists_vertical (hSd U U.property)
        (isOpen_of_mem_countableBasis B.property)
        (nonempty_of_mem_countableBasis B.property))
  filter_upwards [hAll] with x hx
  have hFiber (U : S) : {y : Y | (x, y) ∈ (U : Set (X × Y))} ∈ residual Y := by
    apply residual_of_dense_open
    · exact (hSo U U.property).preimage (continuous_const.prodMk continuous_id)
    · apply dense_iff_inter_open.mpr
      intro V hVo hVn
      obtain ⟨y, hyV⟩ := hVn
      obtain ⟨B, hB, _hyB, hBV⟩ :=
        (isBasis_countableBasis Y).exists_subset_of_mem_open hyV hVo
      obtain ⟨z, hzB, hzx⟩ := hx U ⟨B, hB⟩
      exact ⟨z, hBV hzB, hzx⟩
  have hAllFiber : ∀ᶠ y in residual Y, ∀ U : S, (x, y) ∈ (U : Set (X × Y)) :=
    eventually_countable_forall.mpr hFiber
  filter_upwards [hAllFiber] with y hy
  exact hS (by intro U hU; exact hy ⟨U, hU⟩)

/-- An immediate version with an actual section: a comeager set of pairs
has a comeager vertical section in a nonempty Baire first factor. -/
theorem exists_residual_section [BaireSpace X] [Nonempty X]
    [SecondCountableTopology Y] {P : X × Y → Prop}
    (hP : ∀ᶠ p in residual (X × Y), P p) :
    ∃ x, ∀ᶠ y in residual Y, P (x, y) :=
  (dense_of_mem_residual (eventually_residual_prod hP)).nonempty




end BenchmarkJump
end Source39
end BenchmarkCountableProof

/- Whole source module: CategoryLocal -/
namespace BenchmarkCountableProof
section Source40
open Filter Set Topology TopologicalSpace
open scoped Topology

namespace BenchmarkJump

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A countable Baire cover of a nonempty open set has one member comeager
on a smaller nonempty open set. -/
theorem baire_cover_local_residual [BaireSpace X] {ι : Type*} [Countable ι]
    (A : ι → Set X) (hA : ∀ i, BaireMeasurableSet (A i))
    (Ω : Set X) (hΩ : IsOpen Ω) (hΩn : Ω.Nonempty)
    (hCover : Ω ⊆ ⋃ i, A i) :
    ∃ i, ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ U ⊆ Ω ∧
      ∀ᶠ x in residual X, x ∈ U → x ∈ A i := by
  classical
  have hNon : ∃ i, ¬ IsMeagre (Ω ∩ A i) := by
    by_contra! h
    apply not_isMeagre_of_isOpen hΩ hΩn
    apply (isMeagre_iUnion h).mono
    intro x hxΩ
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hCover hxΩ)
    exact mem_iUnion.mpr ⟨i, hxΩ, hi⟩
  obtain ⟨i, hi⟩ := hNon
  obtain ⟨V, hVo, hEq⟩ := (hΩ.baireMeasurableSet.inter (hA i)).residualEq_isOpen
  have hEq' : ∀ᶠ x in residual X, x ∈ Ω ∩ A i ↔ x ∈ V :=
    Filter.eventuallyEq_set.mp hEq
  have hVn : V.Nonempty := by
    by_contra hn
    have hVe : V = ∅ := not_nonempty_iff_eq_empty.mp hn
    apply hi
    filter_upwards [hEq'] with x hx
    simpa [hVe] using hx
  obtain ⟨x, hxV, hxEq⟩ := (dense_of_mem_residual hEq').inter_open_nonempty V hVo hVn
  have hxΩ := ((hxEq.mpr hxV).1)
  refine ⟨i, V ∩ Ω, hVo.inter hΩ, ⟨x, hxV, hxΩ⟩, inter_subset_right, ?_⟩
  filter_upwards [hEq'] with y hy
  intro hyU
  exact (hy.mpr hyU.1).2

/-- Restricting an ambient comeager assertion to an open subspace preserves
comeagerness. -/
theorem eventually_residual_open_subspace (U : Set X) (hU : IsOpen U)
    {P : X → Prop} (hP : ∀ᶠ x in residual X, P x) :
    ∀ᶠ x : U in residual U, P (x : X) :=
  tendsto_residual_of_isOpenMap continuous_subtype_val hU.isOpenMap_subtype_val hP

/-- A residual assertion on an open subspace is the same as an ambient
residual implication on that open set. -/
theorem eventually_residual_of_open_subspace (U : Set X) (_hU : IsOpen U)
    {P : X → Prop} (hP : ∀ᶠ x : U in residual U, P (x : X)) :
    ∀ᶠ x in residual X, x ∈ U → P x := by
  classical
  have hm : IsMeagre {x : U | ¬ P (x : X)} := by
    simpa only [IsMeagre, compl_setOf, not_not] using hP
  have hImage : IsMeagre ((↑) '' {x : U | ¬ P (x : X)} : Set X) := hm.image_val
  filter_upwards [hImage] with x hx hxU
  by_contra hxP
  exact hx ⟨⟨x, hxU⟩, hxP, rfl⟩



end BenchmarkJump
end Source40
end BenchmarkCountableProof

/- Whole source module: LpCountableAction -/
namespace BenchmarkCountableProof
section Source41
/-! The actual real-sequence Lp translation action and the countable-orbit
Baire cover needed for the reverse countable benchmark obstruction. -/

open Filter Set Topology TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace BenchmarkCountableReverse

abbrev RealSequences := ℕ → ℝ
abbrev Translations (p : ℝ≥0∞) := lp (fun _ : ℕ => ℝ) p

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

local instance : MeasurableSpace (Translations p) := borel (Translations p)
local instance : BorelSpace (Translations p) := ⟨rfl⟩

def coordinates (h : Translations p) : RealSequences := h

lemma continuous_coordinates : Continuous (coordinates p) := lp.uniformContinuous_coe.continuous

def translationAction (a : RealSequences × Translations p) : RealSequences :=
  a.1 + coordinates p a.2

lemma continuous_translationAction : Continuous (translationAction p) :=
  continuous_fst.add ((continuous_coordinates p).comp continuous_snd)

lemma isOpenMap_translationAction : IsOpenMap (translationAction p) := by
  intro W hW
  have heq : translationAction p '' W = ⋃ h : Translations p,
      (fun x : RealSequences => x + coordinates p h) '' {x | (x, h) ∈ W} := by
    ext y
    constructor
    · rintro ⟨⟨x, h⟩, hxh, rfl⟩
      exact mem_iUnion.mpr ⟨h, x, hxh, rfl⟩
    · intro hy
      obtain ⟨h, x, hxh, hxy⟩ := mem_iUnion.mp hy
      exact ⟨(x, h), hxh, hxy⟩
  rw [heq]
  apply isOpen_iUnion
  intro h
  exact isOpenMap_add_right (coordinates p h) _
    (hW.preimage (continuous_id.prodMk continuous_const))

lemma translationAction_lp_related (hp : p ≠ ∞) (a : RealSequences × Translations p) :
    BenchmarkComparisons.LpDifference p.toReal a.1 (translationAction p a) := by
  have hs := (memℓp_gen_iff (p.toReal_pos_iff_ne_top.mpr hp)).mp (lp.memℓp a.2)
  simpa only [BenchmarkComparisons.LpDifference, translationAction, coordinates,
    Pi.add_apply, sub_add_cancel_left, abs_neg, Real.norm_eq_abs] using hs

theorem countable_orbit_rectangle (hp : p ≠ ∞)
    (f : RealSequences → BenchmarkShift.Point) (hf : Measurable f)
    (hF : ∀ x y, BenchmarkComparisons.LpDifference p.toReal x y →
      BenchmarkComparisons.EInfinity (f x) (f y)) :
    ∃ g : BenchmarkShift.Group, ∃ U : Set RealSequences, ∃ W : Set (Translations p),
      IsOpen U ∧ U.Nonempty ∧ IsOpen W ∧ W.Nonempty ∧
      ∀ᶠ a in residual (RealSequences × Translations p),
        a ∈ U ×ˢ W → f (translationAction p a) = BenchmarkShift.shift g (f a.1) := by
  classical
  let B : BenchmarkShift.Group → Set (RealSequences × Translations p) := fun g =>
    {a | f (translationAction p a) = BenchmarkShift.shift g (f a.1)}
  have hB (g : BenchmarkShift.Group) : BaireMeasurableSet (B g) := by
    apply MeasurableSet.baireMeasurableSet
    exact measurableSet_eq_fun (hf.comp (continuous_translationAction p).measurable)
      (((BenchmarkShift.continuous_shift g).measurable.comp hf).comp measurable_fst)
  have hcover : (univ : Set (RealSequences × Translations p)) ⊆ ⋃ g, B g := by
    intro a _
    obtain ⟨g, hg⟩ := hF a.1 (translationAction p a) (translationAction_lp_related p hp a)
    apply mem_iUnion.mpr
    refine ⟨g, ?_⟩
    exact funext hg
  obtain ⟨g, V, hVo, hVn, _hVU, hVres⟩ :=
    BenchmarkJump.baire_cover_local_residual B hB univ isOpen_univ univ_nonempty hcover
  obtain ⟨⟨x, h⟩, hxh⟩ := hVn
  obtain ⟨U, W, hUo, hWo, hxU, hhW, hUW⟩ := isOpen_prod_iff.mp hVo x h hxh
  refine ⟨g, U, W, hUo, ⟨x, hxU⟩, hWo, ⟨h, hhW⟩, ?_⟩
  filter_upwards [hVres] with a ha hrect
  exact ha (hUW hrect)

end BenchmarkCountableReverse
end
end Source41
end BenchmarkCountableProof

/- Whole source module: BoundedDifferenceJump -/
namespace BenchmarkCountableProof
section Source42
/-! The actual bounded-difference relation and its Friedman--Stanley jump,
including the Borel facts and closed exhaustion used in the manuscript. -/

open Filter Set Topology TopologicalSpace
open scoped Topology

namespace BenchmarkJump

abbrev RealSequences := ℕ → ℝ

def UniformBound (n : ℕ) (x y : RealSequences) : Prop :=
  ∀ i, |x i - y i| ≤ (n : ℝ)

def BoundedDifference (x y : RealSequences) : Prop :=
  ∃ n : ℕ, UniformBound n x y

theorem uniformBound_refl (x : RealSequences) : UniformBound 0 x x := by
  intro i
  simp

theorem uniformBound_symm {n : ℕ} {x y : RealSequences}
    (h : UniformBound n x y) : UniformBound n y x := by
  intro i
  simpa only [abs_sub_comm] using h i

theorem uniformBound_trans {n m : ℕ} {x y z : RealSequences}
    (hxy : UniformBound n x y) (hyz : UniformBound m y z) :
    UniformBound (n + m) x z := by
  intro i
  calc
    |x i - z i| ≤ |x i - y i| + |y i - z i| := abs_sub_le _ _ _
    _ ≤ (n : ℝ) + m := add_le_add (hxy i) (hyz i)
    _ = ((n + m : ℕ) : ℝ) := by norm_cast

theorem boundedDifference_equivalence : Equivalence BoundedDifference := by
  constructor
  · intro x
    exact ⟨0, uniformBound_refl x⟩
  · rintro x y ⟨n, h⟩
    exact ⟨n, uniformBound_symm h⟩
  · rintro x y z ⟨n, hn⟩ ⟨m, hm⟩
    exact ⟨n + m, uniformBound_trans hn hm⟩

theorem isClosed_uniformBound (n : ℕ) :
    IsClosed {p : RealSequences × RealSequences | UniformBound n p.1 p.2} := by
  change IsClosed {p : RealSequences × RealSequences | ∀ i, |p.1 i - p.2 i| ≤ (n : ℝ)}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_le
    ((((continuous_apply i).comp continuous_fst).sub
      ((continuous_apply i).comp continuous_snd)).abs) continuous_const

theorem measurableSet_boundedDifference :
    MeasurableSet {p : RealSequences × RealSequences | BoundedDifference p.1 p.2} := by
  change MeasurableSet {p : RealSequences × RealSequences | ∃ n, UniformBound n p.1 p.2}
  simpa only [setOf_exists] using
    MeasurableSet.iUnion (fun n => (isClosed_uniformBound n).measurableSet)

theorem boundedDifference_iff_real_bound (x y : RealSequences) :
    BoundedDifference x y ↔ ∃ C : ℝ, ∀ i, |x i - y i| ≤ C := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨C, hC⟩
    obtain ⟨n, hn⟩ := exists_nat_ge C
    exact ⟨n, fun i => (hC i).trans hn⟩

def BoundedDifferenceJump : (ℕ → RealSequences) → (ℕ → RealSequences) → Prop :=
  Jump BoundedDifference

theorem boundedDifferenceJump_equivalence : Equivalence BoundedDifferenceJump :=
  jump_equivalence BoundedDifference boundedDifference_equivalence

theorem measurableSet_boundedDifferenceJump :
    MeasurableSet {p : (ℕ → RealSequences) × (ℕ → RealSequences) |
      BoundedDifferenceJump p.1 p.2} := by
  have hOne (k l : ℕ) : MeasurableSet
      {p : (ℕ → RealSequences) × (ℕ → RealSequences) |
        BoundedDifference (p.1 k) (p.2 l)} := by
    have hm : Measurable (fun p : (ℕ → RealSequences) × (ℕ → RealSequences) =>
        (p.1 k, p.2 l)) :=
      ((measurable_pi_apply k).comp measurable_fst).prodMk
        ((measurable_pi_apply l).comp measurable_snd)
    exact measurableSet_boundedDifference.preimage hm
  have hFwd : MeasurableSet
      {p : (ℕ → RealSequences) × (ℕ → RealSequences) |
        ∀ k, ∃ l, BoundedDifference (p.1 k) (p.2 l)} := by
    simpa only [setOf_forall, setOf_exists] using
      MeasurableSet.iInter (fun k => MeasurableSet.iUnion (hOne k))
  have hRev : MeasurableSet
      {p : (ℕ → RealSequences) × (ℕ → RealSequences) |
        ∀ l, ∃ k, BoundedDifference (p.1 k) (p.2 l)} := by
    simpa only [setOf_forall, setOf_exists] using
      MeasurableSet.iInter (fun l => MeasurableSet.iUnion (fun k => hOne k l))
  exact hFwd.inter hRev





end BenchmarkJump
end Source42
end BenchmarkCountableProof

/- Whole source module: CircleReduction -/
namespace BenchmarkCountableProof
section Source43
open Filter Topology
open scoped Topology BigOperators ENNReal NNReal

noncomputable section

namespace MeasureEquivalenceCircleReduction

/-!
The domain and codomain sequence spaces below have their product topologies.
The lp relations are actual summability predicates, and the null relations
are actual convergence-to-zero predicates. All chord estimates and the
even/odd real interleaving are proved, rather than supplied as hypotheses.
-/

def circleEmbed (t : UnitAddCircle) : ℂ := AddCircle.toCircle t

lemma continuous_circleEmbed : Continuous circleEmbed :=
  continuous_subtype_val.comp AddCircle.continuous_toCircle

@[simp] lemma circleEmbed_re_mk (r : ℝ) :
    (circleEmbed (r : UnitAddCircle)).re = Real.cos (2 * Real.pi * r) := by
  simp only [circleEmbed, AddCircle.toCircle_apply_mk, div_one, Circle.coe_exp,
    Complex.exp_ofReal_mul_I_re]

@[simp] lemma circleEmbed_im_mk (r : ℝ) :
    (circleEmbed (r : UnitAddCircle)).im = Real.sin (2 * Real.pi * r) := by
  simp only [circleEmbed, AddCircle.toCircle_apply_mk, div_one, Circle.coe_exp,
    Complex.exp_ofReal_mul_I_im]

lemma circle_rep (t : UnitAddCircle) :
    ∃ r : ℝ, (r : UnitAddCircle) = t ∧ |r| ≤ 1 / 2 ∧ ‖t‖ = |r| := by
  obtain ⟨x⟩ := t
  have hz : (((round x : ℤ) : ℝ) : UnitAddCircle) = 0 := by
    apply (AddCircle.coe_eq_zero_iff _).2
    exact ⟨round x, by simp⟩
  refine ⟨x - round x, ?_, abs_sub_round x, UnitAddCircle.norm_eq⟩
  simp [hz]
  rfl

lemma chord_real (r : ℝ) :
    ‖circleEmbed (r : UnitAddCircle) - 1‖ = 2 * |Real.sin (Real.pi * r)| := by
  simp only [circleEmbed, AddCircle.toCircle_apply_mk, div_one, Circle.coe_exp]
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hr : 2 * Real.pi * r / 2 = Real.pi * r := by ring
  rw [hr, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

lemma chord_bounds (t : UnitAddCircle) :
    4 * ‖t‖ ≤ ‖circleEmbed t - 1‖ ∧
    ‖circleEmbed t - 1‖ ≤ (2 * Real.pi) * ‖t‖ := by
  obtain ⟨r, rfl, hr, hn⟩ := circle_rep t
  rw [chord_real, hn]
  have habs : |Real.pi * r| = Real.pi * |r| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hb : |Real.pi * r| ≤ Real.pi / 2 := by
    rw [habs]; nlinarith [Real.pi_pos]
  have hlo := Real.mul_abs_le_abs_sin hb
  have hhi := Real.abs_sin_le_abs (x := Real.pi * r)
  rw [habs] at hlo hhi
  have hcalc : 2 / Real.pi * (Real.pi * |r|) = 2 * |r| := by
    field_simp
  rw [hcalc] at hlo
  constructor <;> nlinarith

lemma circleEmbed_add (s t : UnitAddCircle) :
    circleEmbed (s + t) = circleEmbed s * circleEmbed t := by
  exact congrArg (fun c : Circle => (c : ℂ)) (AddCircle.toCircle_add s t)

@[simp] lemma circleEmbed_norm (t : UnitAddCircle) : ‖circleEmbed t‖ = 1 :=
  (AddCircle.toCircle t).norm_coe

lemma chord_sub (s t : UnitAddCircle) :
    ‖circleEmbed s - circleEmbed t‖ = ‖circleEmbed (s - t) - 1‖ := by
  have hmul : circleEmbed (s - t) * circleEmbed t = circleEmbed s := by
    rw [← circleEmbed_add, sub_add_cancel]
  have heq : circleEmbed s - circleEmbed t =
      (circleEmbed (s - t) - 1) * circleEmbed t := by
    rw [sub_mul, one_mul, hmul]
  rw [heq, norm_mul, circleEmbed_norm, mul_one]

lemma chord_sub_bounds (s t : UnitAddCircle) :
    4 * ‖s - t‖ ≤ ‖circleEmbed s - circleEmbed t‖ ∧
    ‖circleEmbed s - circleEmbed t‖ ≤ (2 * Real.pi) * ‖s - t‖ := by
  rw [chord_sub]
  exact chord_bounds (s - t)

lemma memlp_circle_iff_complex (p : ℝ≥0∞) (x y : ℕ → UnitAddCircle) :
    Memℓp (fun n => x n - y n) p ↔
    Memℓp (fun n => circleEmbed (x n) - circleEmbed (y n)) p := by
  constructor
  · intro h
    exact (h.norm.const_mul (2 * Real.pi)).mono fun n => (chord_sub_bounds _ _).2
  · intro h
    apply (h.norm.const_mul (1 / 4 : ℝ)).mono
    intro n
    have := (chord_sub_bounds (x n) (y n)).1
    linarith

lemma memlp_complex_iff_re_im (p : ℝ≥0∞) (z : ℕ → ℂ) :
    Memℓp z p ↔ Memℓp (fun n => (z n).re) p ∧ Memℓp (fun n => (z n).im) p := by
  constructor
  · intro h
    constructor
    · exact h.norm.mono fun n => Complex.abs_re_le_norm (z n)
    · exact h.norm.mono fun n => Complex.abs_im_le_norm (z n)
  · rintro ⟨hr, hi⟩
    exact (hr.norm.add hi.norm).mono fun n => Complex.norm_le_abs_re_add_abs_im (z n)

def pairCoords (a b : ℕ → ℝ) (i : ℕ × Fin 2) : ℝ :=
  if i.2 = 0 then a i.1 else b i.1

def interleave (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  pairCoords a b (Nat.divModEquiv 2 n)

@[simp] lemma interleave_even (a b : ℕ → ℝ) (n : ℕ) :
    interleave a b (2 * n) = a n := by
  simp [interleave, pairCoords, Nat.divModEquiv, Nat.mul_comm]

@[simp] lemma interleave_odd (a b : ℕ → ℝ) (n : ℕ) :
    interleave a b (2 * n + 1) = b n := by
  simp [interleave, pairCoords, Nat.divModEquiv, Nat.mul_comm]
  have hd : (n * 2 + 1) / 2 = n := by omega
  have hm : ¬ 2 ∣ n * 2 + 1 := by omega
  simp [hm, hd]

lemma interleave_sub (a b c d : ℕ → ℝ) :
    interleave a b - interleave c d = interleave (a - c) (b - d) := by
  ext n
  simp only [interleave, pairCoords, Pi.sub_apply]
  split_ifs <;> rfl

lemma memlp_interleave (p : ℝ≥0∞) (hp : 0 < p.toReal) (a b : ℕ → ℝ) :
    Memℓp (interleave a b) p ↔ Memℓp a p ∧ Memℓp b p := by
  simp only [memℓp_gen_iff hp]
  change Summable ((fun i : ℕ × Fin 2 => ‖pairCoords a b i‖ ^ p.toReal) ∘
    Nat.divModEquiv 2) ↔ _
  rw [(Nat.divModEquiv 2).summable_iff]
  constructor
  · intro h
    constructor
    · simpa [Function.comp_def, pairCoords] using
        h.comp_injective (f := fun i : ℕ × Fin 2 => ‖pairCoords a b i‖ ^ p.toReal)
          (i := fun n : ℕ => (n, (0 : Fin 2))) (by intro n m h; exact congrArg Prod.fst h)
    · simpa [Function.comp_def, pairCoords] using
        h.comp_injective (f := fun i : ℕ × Fin 2 => ‖pairCoords a b i‖ ^ p.toReal)
          (i := fun n : ℕ => (n, (1 : Fin 2))) (by intro n m h; exact congrArg Prod.fst h)
  · rintro ⟨ha, hb⟩
    apply (summable_prod_of_nonneg (by intro i; positivity)).2
    constructor
    · intro n
      exact (hasSum_fintype (fun j : Fin 2 => ‖pairCoords a b (n, j)‖ ^ p.toReal)).summable
    · simpa [tsum_fintype, Fin.sum_univ_two, pairCoords] using ha.add hb

def realEmbed (x : ℕ → UnitAddCircle) : ℕ → ℝ :=
  interleave (fun n => (circleEmbed (x n)).re) (fun n => (circleEmbed (x n)).im)

lemma continuous_realEmbed : Continuous realEmbed := by
  apply continuous_pi
  intro n
  dsimp [realEmbed, interleave, pairCoords]
  split_ifs
  · exact Complex.continuous_re.comp (continuous_circleEmbed.comp (continuous_apply _))
  · exact Complex.continuous_im.comp (continuous_circleEmbed.comp (continuous_apply _))

@[simp] lemma realEmbed_even (x : ℕ → UnitAddCircle) (n : ℕ) :
    realEmbed x (2 * n) = (circleEmbed (x n)).re := by simp [realEmbed]

@[simp] lemma realEmbed_odd (x : ℕ → UnitAddCircle) (n : ℕ) :
    realEmbed x (2 * n + 1) = (circleEmbed (x n)).im := by simp [realEmbed]

def CircleLpRel (p : ℝ≥0∞) (x y : ℕ → UnitAddCircle) : Prop :=
  Memℓp (fun n => x n - y n) p

def RealLpRel (p : ℝ≥0∞) (x y : ℕ → ℝ) : Prop :=
  Memℓp (fun n => x n - y n) p

theorem circle_real_lp_reduction (p : ℝ≥0∞) (hp : 0 < p.toReal)
    (x y : ℕ → UnitAddCircle) :
    CircleLpRel p x y ↔ RealLpRel p (realEmbed x) (realEmbed y) := by
  rw [CircleLpRel, memlp_circle_iff_complex, memlp_complex_iff_re_im]
  change _ ↔ Memℓp (realEmbed x - realEmbed y) p
  rw [realEmbed, realEmbed, interleave_sub, memlp_interleave p hp]
  rfl

lemma null_circle_iff_complex (x y : ℕ → UnitAddCircle) :
    Tendsto (fun n => x n - y n) atTop (𝓝 0) ↔
    Tendsto (fun n => circleEmbed (x n) - circleEmbed (y n)) atTop (𝓝 0) := by
  conv_lhs => rw [tendsto_zero_iff_norm_tendsto_zero]
  conv_rhs => rw [tendsto_zero_iff_norm_tendsto_zero]
  constructor
  · intro h
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => (chord_sub_bounds (x n) (y n)).2)
    simpa using h.const_mul (2 * Real.pi)
  · intro h
    apply squeeze_zero (fun n => norm_nonneg _)
      (g := fun n => (1 / 4 : ℝ) * ‖circleEmbed (x n) - circleEmbed (y n)‖)
    · intro n
      have := (chord_sub_bounds (x n) (y n)).1
      linarith
    · simpa using h.const_mul (1 / 4 : ℝ)

lemma null_interleave (a b : ℕ → ℝ) :
    Tendsto (interleave a b) atTop (𝓝 0) ↔
    Tendsto a atTop (𝓝 0) ∧ Tendsto b atTop (𝓝 0) := by
  simp only [Metric.tendsto_atTop]
  constructor
  · intro h
    constructor
    · intro ε hε
      obtain ⟨N, hN⟩ := h ε hε
      refine ⟨N, fun n hn => ?_⟩
      simpa using hN (2 * n) (by omega)
    · intro ε hε
      obtain ⟨N, hN⟩ := h ε hε
      refine ⟨N, fun n hn => ?_⟩
      simpa using hN (2 * n + 1) (by omega)
  · rintro ⟨ha, hb⟩ ε hε
    obtain ⟨Na, hNa⟩ := ha ε hε
    obtain ⟨Nb, hNb⟩ := hb ε hε
    refine ⟨2 * max Na Nb, fun n hn => ?_⟩
    have hna : Na ≤ n / 2 := by omega
    have hnb : Nb ≤ n / 2 := by omega
    change dist (if (Nat.divModEquiv 2 n).2 = 0 then a (n / 2) else b (n / 2)) 0 < ε
    split_ifs
    · exact hNa _ hna
    · exact hNb _ hnb

def CircleNullRel (x y : ℕ → UnitAddCircle) : Prop :=
  Tendsto (fun n => x n - y n) atTop (𝓝 0)

def RealNullRel (x y : ℕ → ℝ) : Prop :=
  Tendsto (fun n => x n - y n) atTop (𝓝 0)

theorem circle_real_null_reduction (x y : ℕ → UnitAddCircle) :
    CircleNullRel x y ↔ RealNullRel (realEmbed x) (realEmbed y) := by
  rw [CircleNullRel, null_circle_iff_complex]
  change _ ↔ Tendsto (realEmbed x - realEmbed y) atTop (𝓝 0)
  rw [realEmbed, realEmbed, interleave_sub, null_interleave]
  constructor
  · intro h
    constructor
    · change Tendsto (fun n => (circleEmbed (x n)).re - (circleEmbed (y n)).re) atTop (𝓝 0)
      simpa only [Function.comp_def, Complex.sub_re, Complex.zero_re] using
        Complex.continuous_re.continuousAt.tendsto.comp h
    · change Tendsto (fun n => (circleEmbed (x n)).im - (circleEmbed (y n)).im) atTop (𝓝 0)
      simpa only [Function.comp_def, Complex.sub_im, Complex.zero_im] using
        Complex.continuous_im.continuousAt.tendsto.comp h
  · rintro ⟨hr, hi⟩
    apply tendsto_zero_iff_norm_tendsto_zero.2
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => Complex.norm_le_abs_re_add_abs_im _)
    simpa using hr.norm.add hi.norm

/-- The concrete cos/sin interleaving reduces the real-exponent summability relations. -/
theorem circle_real_lp_reduction_real (p : ℝ) (hp : 1 ≤ p)
    (x y : ℕ → UnitAddCircle) :
    (Summable fun n => ‖x n - y n‖ ^ p) ↔
    Summable (fun n => |realEmbed x n - realEmbed y n| ^ p) := by
  have hp0 : 0 ≤ p := by linarith
  have hpt : 0 < (ENNReal.ofReal p).toReal := by
    rw [ENNReal.toReal_ofReal hp0]
    linarith
  simpa only [CircleLpRel, RealLpRel, memℓp_gen_iff hpt,
    ENNReal.toReal_ofReal hp0, Real.norm_eq_abs] using
    circle_real_lp_reduction (ENNReal.ofReal p) hpt x y

/-- A single continuous map works for every finite real exponent p >= 1 and for c0. -/
theorem compact_circle_reductions :
    ∃ b : (ℕ → UnitAddCircle) → (ℕ → ℝ), Continuous b ∧
      (∀ p : ℝ, 1 ≤ p → ∀ x y,
        (Summable fun n => ‖x n - y n‖ ^ p) ↔
        Summable (fun n => |b x n - b y n| ^ p)) ∧
      (∀ x y, Tendsto (fun n => x n - y n) atTop (𝓝 0) ↔
        Tendsto (fun n => b x n - b y n) atTop (𝓝 0)) := by
  exact ⟨realEmbed, continuous_realEmbed, circle_real_lp_reduction_real,
    circle_real_null_reduction⟩







end MeasureEquivalenceCircleReduction
end
end Source43
end BenchmarkCountableProof

/- Whole source module: CircleCategory -/
namespace BenchmarkCountableProof
section Source44
/-! The concrete category properties of null difference on the compact
product of circles. These are the source-side category hypotheses of the
first jump obstruction, proved here without assuming the obstruction. -/

open Filter Set Topology TopologicalSpace
open scoped Topology

namespace BenchmarkJump

abbrev CircleSequences := ℕ → UnitAddCircle
abbrev CircleNullDifference := MeasureEquivalenceCircleReduction.CircleNullRel

def CircleTailBound (a : CircleSequences) (N : ℕ) : Set CircleSequences :=
  {x | ∀ n, N ≤ n → ‖x n - a n‖ ≤ (1 / 8 : ℝ)}

theorem isClosed_circleTailBound (a : CircleSequences) (N : ℕ) :
    IsClosed (CircleTailBound a N) := by
  change IsClosed {x : CircleSequences | ∀ n, N ≤ n → ‖x n - a n‖ ≤ (1 / 8 : ℝ)}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro n
  apply isClosed_iInter
  intro _hn
  exact isClosed_le (((continuous_apply n).sub continuous_const).norm) continuous_const

theorem interior_circleTailBound (a : CircleSequences) (N : ℕ) :
    interior (CircleTailBound a N) = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  intro x hx
  obtain ⟨I, V, hV, hVI⟩ := isOpen_pi_iff.mp isOpen_interior x hx
  let n : ℕ := max N (I.sup id + 1)
  have hNn : N ≤ n := le_max_left _ _
  have hnI : n ∉ I := by
    intro hn
    have hle : n ≤ I.sup id := Finset.le_sup (f := id) hn
    have hlt : I.sup id < n := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
    omega
  let y : CircleSequences := Function.update x n (a n + ((1 / 2 : ℝ) : UnitAddCircle))
  have hy : y ∈ (I : Set ℕ).pi V := by
    intro i hi
    have hin : i ≠ n := by intro h; exact hnI (h ▸ hi)
    simpa only [y, Function.update_of_ne hin] using (hV i hi).2
  have hbad := interior_subset (hVI hy) n hNn
  have hnorm : ‖((1 / 2 : ℝ) : UnitAddCircle)‖ = (1 / 2 : ℝ) := by
    simpa using AddCircle.norm_half_period_eq (1 : ℝ)
  simp [y, hnorm] at hbad
  norm_num at hbad

theorem isNowhereDense_circleTailBound (a : CircleSequences) (N : ℕ) :
    IsNowhereDense (CircleTailBound a N) :=
  (isClosed_circleTailBound a N).isNowhereDense_iff.mpr (interior_circleTailBound a N)

/-- Every actual null-difference class in the compact circle product is meager. -/
theorem circleNullDifference_class_meagre (a : CircleSequences) :
    IsMeagre {x | CircleNullDifference x a} := by
  apply (isMeagre_iUnion (fun N => (isNowhereDense_circleTailBound a N).isMeagre)).mono
  intro x hx
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hx (1 / 8 : ℝ) (by norm_num)
  exact mem_iUnion.2 ⟨N, fun n hn => by simpa only [dist_zero_right] using (hN n hn).le⟩

def FinitelySupportedCircle (h : CircleSequences) : Prop :=
  ∃ I : Finset ℕ, ∀ n, n ∉ I → h n = 0

theorem circleNullDifference_translate (h : CircleSequences)
    (hh : FinitelySupportedCircle h) (x : CircleSequences) :
    CircleNullDifference x (x + h) := by
  obtain ⟨I, hI⟩ := hh
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (I.sup id)] with n hn
  have hnI : n ∉ I := by
    intro hi
    exact (not_le_of_gt hn) (Finset.le_sup (f := id) hi)
  simp [hI n hnI]

/-- Finite-coordinate translations can move each point into any prescribed
nonempty product-open set. -/
theorem finite_translate_into_open (U : Set CircleSequences)
    (hU : IsOpen U) (hne : U.Nonempty) (x : CircleSequences) :
    ∃ h : CircleSequences, FinitelySupportedCircle h ∧ x + h ∈ U := by
  classical
  obtain ⟨u, hu⟩ := hne
  obtain ⟨I, V, hV, hVI⟩ := isOpen_pi_iff.mp hU u hu
  let h : CircleSequences := fun i => if i ∈ I then u i - x i else 0
  refine ⟨h, ⟨I, fun n hn => by simp [h, hn]⟩, hVI ?_⟩
  intro i hi
  change i ∈ I at hi
  simpa [h, hi] using (hV i hi).2

/-- Generic ergodicity of the concrete compact-circle null-difference
relation. A countable open subcover is extracted from finite-coordinate
translations; no unproved countability of the whole translating group is used. -/
theorem circleNullDifference_genericallyErgodic :
    GenericallyErgodic CircleNullDifference := by
  classical
  intro A hA hInv
  by_cases hm : IsMeagre A
  · exact Or.inl hm
  right
  obtain ⟨U, hUo, hAU⟩ := hA.residualEq_isOpen
  have hAU' : ∀ᶠ x in residual CircleSequences, x ∈ A ↔ x ∈ U :=
    Filter.eventuallyEq_set.mp hAU
  have hUne : U.Nonempty := by
    by_contra hn
    have hUe : U = ∅ := not_nonempty_iff_eq_empty.mp hn
    apply hm
    filter_upwards [hAU'] with x hx
    simp [hUe] at hx
    exact hx
  choose h hh hmem using finite_translate_into_open U hUo hUne
  let V : CircleSequences → Set CircleSequences := fun x => {y | y + h x ∈ U}
  have hVnhds (x : CircleSequences) : V x ∈ 𝓝 x :=
    (hUo.preimage (continuous_id.add continuous_const)).mem_nhds (hmem x)
  obtain ⟨S, hScount, hScover⟩ := TopologicalSpace.countable_cover_nhds hVnhds
  have hAll : ∀ᶠ y in residual CircleSequences, ∀ x ∈ S,
      y + h x ∈ A ↔ y + h x ∈ U := by
    apply eventually_countable_ball hScount |>.2
    intro x _hx
    exact tendsto_residual_of_isOpenMap
      (continuous_id.add continuous_const) (isOpenMap_add_right (h x)) hAU'
  filter_upwards [hAll] with y hy
  have hycover : y ∈ ⋃ x ∈ S, V x := by rw [hScover]; trivial
  obtain ⟨x, hx⟩ := mem_iUnion.1 hycover
  obtain ⟨hxS, hyV⟩ := mem_iUnion.1 hx
  have hyA : y + h x ∈ A := (hy x hxS).mpr hyV
  exact (hInv y (y + h x) (circleNullDifference_translate (h x) (hh x) y)).mpr hyA




end BenchmarkJump
end Source44
end BenchmarkCountableProof

/- Whole source module: FiniteFourier -/
namespace BenchmarkCountableProof
section Source45
/-!
Finite Hilbert-valued Fourier identities for the finite-torus feasibility check.
This file is a separate development and does not alter the earlier checks.
-/

open scoped BigOperators ComplexConjugate

namespace MeasureEquivalenceFourier

variable {G E : Type*} [AddCommGroup G] [Fintype G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma character_orthogonality_sum (χ ψ : AddChar G ℂ) :
    (∑ x, conj (χ x) * ψ x) =
      if χ = ψ then (Fintype.card G : ℂ) else 0 := by
  classical
  have h := AddChar.wInner_cWeight_eq_boole χ ψ
  simp only [RCLike.wInner_cWeight_eq_expect, RCLike.inner_apply,
    Fintype.expect_eq_sum_div_card] at h
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  split_ifs with heq
  · simp only [heq, ite_true] at h
    have hh := (div_eq_iff hc).mp h
    simpa [heq, mul_comm] using hh
  · simp only [heq, ite_false] at h
    have hh := (div_eq_iff hc).mp h
    simpa [mul_comm] using hh

lemma synthesis_inner (v w : AddChar G ℂ → E) :
    (∑ x, inner ℂ (∑ χ : AddChar G ℂ, χ x • v χ)
      (∑ ψ : AddChar G ℂ, ψ x • w ψ)) =
      (Fintype.card G : ℂ) * ∑ χ : AddChar G ℂ, inner ℂ (v χ) (w χ) := by
  classical
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  calc
    (∑ x, ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ,
        conj (χ x) * (ψ x * inner ℂ (v χ) (w ψ))) =
        ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ,
          (∑ x, conj (χ x) * ψ x) * inner ℂ (v χ) (w ψ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ψ _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (Fintype.card G : ℂ) *
        ∑ χ : AddChar G ℂ, inner ℂ (v χ) (w χ) := by
      simp_rw [character_orthogonality_sum]
      simp [Finset.mul_sum]

theorem synthesis_parseval (v : AddChar G ℂ → E) :
    (∑ x, ‖∑ χ : AddChar G ℂ, χ x • v χ‖ ^ 2) =
      (Fintype.card G : ℝ) * ∑ χ : AddChar G ℂ, ‖v χ‖ ^ 2 := by
  have h := synthesis_inner v v
  simp only [inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

noncomputable def coefficient (F : G → E) (χ : AddChar G ℂ) : E :=
  (Fintype.card G : ℂ)⁻¹ • ∑ y, conj (χ y) • F y

theorem inversion (F : G → E) (x : G) :
    (∑ χ : AddChar G ℂ, χ x • coefficient F χ) = F x := by
  classical
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hχ (χ : AddChar G ℂ) (y : G) :
      χ x * conj (χ y) = χ (x - y) := by
    rw [χ.map_sub_eq_div, div_eq_mul_inv, χ.inv_apply_eq_conj]
  calc
    (∑ χ : AddChar G ℂ, χ x • coefficient F χ) =
        (Fintype.card G : ℂ)⁻¹ • ∑ y,
          (∑ χ : AddChar G ℂ, χ (x - y)) • F y := by
      simp only [coefficient, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro χ _
      rw [← hχ]
      congr 1
      ring
    _ = (Fintype.card G : ℂ)⁻¹ • ((Fintype.card G : ℂ) • F x) := by
      simp [AddChar.sum_apply_eq_ite, sub_eq_zero]
    _ = F x := by simp [smul_smul, hc]

theorem translation_energy (F : G → E) (a : G) :
    (∑ x, ‖F (x + a) - F x‖ ^ 2) =
      (Fintype.card G : ℝ) *
        ∑ χ : AddChar G ℂ, ‖χ a - 1‖ ^ 2 * ‖coefficient F χ‖ ^ 2 := by
  have hpoint (x : G) : F (x + a) - F x =
      ∑ χ : AddChar G ℂ, χ x • ((χ a - 1) • coefficient F χ) := by
    rw [← inversion F (x + a), ← inversion F x, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro χ _
    rw [χ.map_add_eq_mul, mul_smul, sub_smul, one_smul, smul_sub]
  simp_rw [hpoint]
  rw [synthesis_parseval]
  simp [norm_smul, mul_pow]

lemma translation_family_energy {K : Type*} [Fintype K] (c : K → G) (F : G → E) :
      (∑ i, ∑ x, ‖F (x + c i) - F x‖ ^ 2) =
        (Fintype.card G : ℝ) * ∑ χ : AddChar G ℂ,
          (∑ i, ‖χ (c i) - 1‖ ^ 2) * ‖coefficient F χ‖ ^ 2 := by
  simp_rw [translation_energy]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [Finset.sum_mul]

/-- A comparison of scalar Fourier multipliers gives the same comparison
for every function with values in a complex inner product space. -/
theorem spectral_comparison {I J : Type*} [Fintype I] [Fintype J]
    (a : I → G) (b : J → G) (C : ℝ)
    (hmult : ∀ χ : AddChar G ℂ,
      (∑ i, ‖χ (a i) - 1‖ ^ 2) ≤ C * ∑ j, ‖χ (b j) - 1‖ ^ 2)
    (F : G → E) :
    (∑ i, ∑ x, ‖F (x + a i) - F x‖ ^ 2) ≤
      C * ∑ j, ∑ x, ‖F (x + b j) - F x‖ ^ 2 := by
  rw [translation_family_energy a F, translation_family_energy b F]
  calc
    (Fintype.card G : ℝ) * ∑ χ : AddChar G ℂ,
        (∑ i, ‖χ (a i) - 1‖ ^ 2) * ‖coefficient F χ‖ ^ 2 ≤
        (Fintype.card G : ℝ) * ∑ χ : AddChar G ℂ,
          (C * ∑ j, ‖χ (b j) - 1‖ ^ 2) * ‖coefficient F χ‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum fun χ _ =>
        mul_le_mul_of_nonneg_right (hmult χ) (sq_nonneg _)
    _ = C * ((Fintype.card G : ℝ) * ∑ χ : AddChar G ℂ,
        (∑ j, ‖χ (b j) - 1‖ ^ 2) * ‖coefficient F χ‖ ^ 2) := by
      simp_rw [mul_assoc, ← Finset.mul_sum]
      ring

end MeasureEquivalenceFourier
end Source45
end BenchmarkCountableProof

/- Whole source module: ScalarMultiplier -/
namespace BenchmarkCountableProof
section Source46
/-!
# Scalar finite-product estimate

This file verifies only an elementary scalar estimate used in a Fourier argument.
It does not formalize Parseval's identity, the trigonometric multiplier bound,
or any theorem about Borel reducibility or equivalence of measures.
-/

open scoped BigOperators

namespace MeasureEquivalenceScalar

/-- A reciprocal form of Bernoulli's inequality, proved by induction. -/
theorem reciprocal_bernoulli (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    (1 + (n : ℝ) * a) * (1 - a) ^ n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 ≤ (1 - a) ^ n := pow_nonneg (sub_nonneg.mpr ha1) _
    calc
      (1 + ((n + 1 : ℕ) : ℝ) * a) * (1 - a) ^ (n + 1) =
          ((1 + (n : ℝ) * a) - ((n : ℝ) + 1) * a ^ 2) * (1 - a) ^ n := by
            push_cast
            rw [pow_succ]
            ring
      _ ≤ (1 + (n : ℝ) * a) * (1 - a) ^ n := by
        apply mul_le_mul_of_nonneg_right _ hp
        have hsq : 0 ≤ ((n : ℝ) + 1) * a ^ 2 := by positivity
        linarith
      _ ≤ 1 := ih

/-- The quantitative loss in a power, valid when the total loss is at most one. -/
theorem power_loss (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ)
    (hna : (n : ℝ) * a ≤ 1) :
    (1 - a) ^ n ≤ 1 - (n : ℝ) * a / 2 := by
  have hx0 : 0 ≤ (n : ℝ) * a := mul_nonneg (Nat.cast_nonneg _) ha
  have hx2 : ((n : ℝ) * a) ^ 2 ≤ (n : ℝ) * a := by nlinarith
  have hden : 0 < 1 + (n : ℝ) * a := by positivity
  apply (mul_le_mul_iff_right₀ hden).mp
  calc
    (1 + (n : ℝ) * a) * (1 - a) ^ n ≤ 1 := reciprocal_bernoulli a ha ha1 n
    _ ≤ (1 + (n : ℝ) * a) * (1 - (n : ℝ) * a / 2) := by nlinarith

/--
If every scalar has absolute value at most one and `t.card` marked scalars
have absolute value at most `1-a`, the product loses at least `t.card*a/2`.
The factors may be negative, and both finite sets may be empty.
-/
theorem finite_product_loss {ι : Type*} (s t : Finset ι) (q : ι → ℝ) (a : ℝ)
    (hts : t ⊆ s) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : ∀ i ∈ s, |q i| ≤ 1)
    (hmarked : ∀ i ∈ t, |q i| ≤ 1 - a)
    (hra : (t.card : ℝ) * a ≤ 1) :
    (t.card : ℝ) * a / 2 ≤ 1 - ∏ i ∈ s, q i := by
  have hprod : (∏ i ∈ s, q i) ≤ (1 - a) ^ t.card := by
    calc
      (∏ i ∈ s, q i) ≤ |∏ i ∈ s, q i| := le_abs_self _
      _ = ∏ i ∈ s, |q i| := Finset.abs_prod s q
      _ ≤ ∏ i ∈ t, |q i| :=
        Finset.prod_le_prod_of_subset_of_le_one hts
          (fun i _ => abs_nonneg (q i)) (fun i hi _ => hq i hi)
      _ ≤ ∏ _i ∈ t, (1 - a) :=
        Finset.prod_le_prod (fun i _ => abs_nonneg (q i)) hmarked
      _ = (1 - a) ^ t.card := by simp
  have hp := power_loss a ha ha1 t.card hra
  linarith

/--
Specialization to the multiplier loss `a = 1/m^2`.  The parameter `m` is real,
so this also applies to positive integer torus sizes after coercion.
-/
theorem square_scale_multiplier {ι : Type*} (s t : Finset ι) (q : ι → ℝ) (m : ℝ)
    (hts : t ⊆ s) (hm : 1 ≤ m)
    (hq : ∀ i ∈ s, |q i| ≤ 1)
    (hmarked : ∀ i ∈ t, |q i| ≤ 1 - 1 / m ^ 2)
    (hr : (t.card : ℝ) ≤ m ^ 2) :
    4 * (t.card : ℝ) ≤ 4 * m ^ 2 * (2 * (1 - ∏ i ∈ s, q i)) := by
  have hmpos : 0 < m := by linarith
  have hm2pos : 0 < m ^ 2 := sq_pos_of_pos hmpos
  have hm2one : 1 ≤ m ^ 2 := by nlinarith
  have ha0 : 0 ≤ 1 / m ^ 2 := by positivity
  have ha1 : 1 / m ^ 2 ≤ 1 := (div_le_one hm2pos).mpr hm2one
  have hra : (t.card : ℝ) * (1 / m ^ 2) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one hm2pos).mpr hr
  have h := finite_product_loss s t q (1 / m ^ 2) hts ha0 ha1 hq hmarked hra
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hm2pos)
  field_simp [ne_of_gt hmpos] at hmul
  nlinarith

end MeasureEquivalenceScalar
end Source46
end BenchmarkCountableProof

/- Whole source module: TrigMultiplier -/
namespace BenchmarkCountableProof
section Source47
/-!
# Trigonometric coordinate multiplier

This file checks the real-variable estimate used for each nonzero Fourier
coordinate.  In particular it applies to integer frequencies, without assuming
integrality.  It does not formalize the Fourier expansion or Parseval's identity.
-/

namespace MeasureEquivalenceTrig

/-- Jordan's inequality after scaling to a circle coordinate. -/
theorem scaled_jordan (m k : ℝ) (hm : 0 < m) (hk : 0 ≤ k)
    (hkm : k ≤ m / 2) :
    2 * k / m ≤ Real.sin (Real.pi * k / m) := by
  have hx0 : 0 ≤ Real.pi * k / m := by positivity
  have hx1 : Real.pi * k / m ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hm).mpr
    nlinarith [Real.pi_pos]
  have h := Real.mul_le_sin hx0 hx1
  calc
    2 * k / m = 2 / Real.pi * (Real.pi * k / m) := by
      field_simp [Real.pi_ne_zero]
    _ ≤ Real.sin (Real.pi * k / m) := h

/-- The sine is bounded away from zero throughout the central frequency range. -/
theorem sine_frequency_lower (m k : ℝ) (hm : 2 ≤ m)
    (hk1 : 1 ≤ k) (hkm1 : k ≤ m - 1) :
    2 / m ≤ Real.sin (Real.pi * k / m) := by
  have hmpos : 0 < m := by linarith
  by_cases hkhalf : k ≤ m / 2
  · have hj := scaled_jordan m k hmpos (by linarith) hkhalf
    have hleft : 2 / m ≤ 2 * k / m := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hmpos)
      linarith
    exact hleft.trans hj
  · have hk' : 1 ≤ m - k := by linarith
    have hkhalf' : m - k ≤ m / 2 := by linarith
    have hj := scaled_jordan m (m - k) hmpos (by linarith) hkhalf'
    have hleft : 2 / m ≤ 2 * (m - k) / m := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hmpos)
      linarith
    have hangle : Real.pi * (m - k) / m = Real.pi - Real.pi * k / m := by
      field_simp [ne_of_gt hmpos]
    rw [hangle, Real.sin_pi_sub] at hj
    exact hleft.trans hj

/--
The coordinate multiplier has a uniform absolute-value gap.  This is valid for
every real `m ≥ 2` and every real `k ∈ [1,m-1]`.
-/
theorem trig_coordinate_bound (m k : ℝ) (hm : 2 ≤ m)
    (hk1 : 1 ≤ k) (hkm1 : k ≤ m - 1) :
    |(1 + 2 * Real.cos (2 * Real.pi * k / m)) / 3| ≤ 1 - 1 / m ^ 2 := by
  have hmpos : 0 < m := by linarith
  have hm2pos : 0 < m ^ 2 := sq_pos_of_pos hmpos
  have hs := sine_frequency_lower m k hm hk1 hkm1
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ 2 / m) hs 2
  have hsquare' : 4 * (1 / m ^ 2) ≤ Real.sin (Real.pi * k / m) ^ 2 := by
    convert hsquare using 1
    ring
  have hangle : 2 * Real.pi * k / m = 2 * (Real.pi * k / m) := by ring
  have hcos : Real.cos (2 * Real.pi * k / m) =
      1 - 2 * Real.sin (Real.pi * k / m) ^ 2 := by
    rw [hangle, Real.cos_two_mul_eq_one_sub]
  have hsmall : 1 / m ^ 2 ≤ (1 : ℝ) / 4 := by
    apply (div_le_div_iff₀ hm2pos (by norm_num : (0 : ℝ) < 4)).mpr
    nlinarith
  have hnonneg : 0 ≤ 1 / m ^ 2 := by positivity
  have hcoslower := Real.neg_one_le_cos (2 * Real.pi * k / m)
  apply abs_le.mpr
  constructor
  · nlinarith
  · nlinarith

end MeasureEquivalenceTrig
end Source47
end BenchmarkCountableProof

/- Whole source module: FiniteTorus -/
namespace BenchmarkCountableProof
section Source48
/-!
Finite product tori: arbitrary single-coordinate shifts compared with the
uniform three-point product walk. This is stronger than the half-turn case.
-/

open scoped BigOperators ComplexConjugate

namespace MeasureEquivalenceTorus

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} [NeZero m]

def axisHom (j : ι) : ZMod m →+ (ι → ZMod m) where
  toFun u i := if i = j then u else 0
  map_zero' := by ext i; simp
  map_add' a b := by ext i; by_cases h : i = j <;> simp [h]

noncomputable def coordinateChar (χ : AddChar (ι → ZMod m) ℂ) (j : ι) :
    AddChar (ZMod m) ℂ := χ.compAddMonoidHom (axisHom j)

lemma char_map_sum {A : Type*} [AddCommGroup A] (χ : AddChar A ℂ)
    {J : Type*} (s : Finset J) (f : J → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, χ.map_add_eq_mul, ih]

omit [NeZero m] in
lemma char_factor (χ : AddChar (ι → ZMod m) ℂ) (x : ι → ZMod m) :
    χ x = ∏ j, coordinateChar χ j (x j) := by
  have hx : x = ∑ j, axisHom j (x j) := by
    ext i
    simp [axisHom]
  conv_lhs => rw [hx, char_map_sum]
  rfl

def step (t : Fin 3) : ZMod m := ![-1, 0, 1] t

def shortShift (ε : ι → Fin 3) : ι → ZMod m := fun j => step (ε j)

noncomputable def q (χ : AddChar (ι → ZMod m) ℂ) (j : ι) : ℝ :=
  (1 + 2 * (coordinateChar χ j 1).re) / 3

omit [Fintype ι] in
lemma coordinate_step_sum (χ : AddChar (ι → ZMod m) ℂ) (j : ι) :
    (∑ t : Fin 3, coordinateChar χ j (step t)) = (3 : ℂ) * q χ j := by
  simp only [Fin.sum_univ_three, step, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, AddChar.map_zero_eq_one, AddChar.map_neg_eq_conj]
  apply Complex.ext <;> simp [q]
  ring

lemma random_character_sum (χ : AddChar (ι → ZMod m) ℂ) :
    (∑ ε : ι → Fin 3, χ (shortShift ε)) =
      (3 : ℂ) ^ Fintype.card ι * (∏ j, q χ j : ℝ) := by
  simp_rw [char_factor]
  change (∑ ε : ι → Fin 3, ∏ j, coordinateChar χ j (step (ε j))) = _
  rw [← Fintype.prod_sum (fun (j : ι) (t : Fin 3) => coordinateChar χ j (step t))]
  simp_rw [coordinate_step_sum]
  simp [Finset.prod_mul_distrib]

lemma random_energy_multiplier (χ : AddChar (ι → ZMod m) ℂ) :
    (∑ ε : ι → Fin 3, ‖χ (shortShift ε) - 1‖ ^ 2) =
      (3 : ℝ) ^ Fintype.card ι * (2 * (1 - ∏ j, q χ j)) := by
  have hre : (∑ ε : ι → Fin 3, (χ (shortShift ε)).re) =
      (3 : ℝ) ^ Fintype.card ι * ∏ j, q χ j := by
    have h := congrArg Complex.re (random_character_sum χ)
    have hreal : (3 : ℂ) ^ Fintype.card ι * (∏ j, q χ j : ℝ) =
        (((3 : ℝ) ^ Fintype.card ι * ∏ j, q χ j : ℝ) : ℂ) := by push_cast; rfl
    rw [hreal] at h
    simpa only [Complex.re_sum, Complex.ofReal_re] using h
  simp_rw [Complex.norm_sub_one_sq_eq_of_norm_eq_one (χ.norm_apply _)]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [hre]
  ring

noncomputable def frequency (χ : AddChar (ι → ZMod m) ℂ) (j : ι) : ZMod m :=
  AddChar.zmodAddEquiv.symm (coordinateChar χ j)

omit [Fintype ι] in
lemma coordinateChar_frequency (χ : AddChar (ι → ZMod m) ℂ) (j : ι) :
    coordinateChar χ j = AddChar.zmodAddEquiv (frequency χ j) := by
  simp [frequency]

lemma zmod_frequency_one (k : ZMod m) :
    ((AddChar.zmodAddEquiv k) 1).re =
      Real.cos (2 * Real.pi * (k.val : ℝ) / (m : ℝ)) := by
  change ((AddChar.zmod m k 1 : Circle) : ℂ).re = _
  have h := AddChar.zmod_intCast m (k.val : ℤ) (1 : ℤ)
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_one,
    mul_one] at h
  rw [h, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  congr 1
  ring

omit [Fintype ι] in
lemma q_abs_le_one (χ : AddChar (ι → ZMod m) ℂ) (j : ι) : |q χ j| ≤ 1 := by
  have h := Complex.abs_re_le_norm (coordinateChar χ j 1)
  rw [(coordinateChar χ j).norm_apply] at h
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  unfold q
  exact abs_le.mpr ⟨by linarith, by linarith⟩

omit [Fintype ι] in
lemma q_abs_gap (χ : AddChar (ι → ZMod m) ℂ) (hm : 2 ≤ m) (j : ι)
    (hj : frequency χ j ≠ 0) : |q χ j| ≤ 1 - 1 / (m : ℝ) ^ 2 := by
  have hk1 : 1 ≤ ((frequency χ j).val : ℝ) := by
    exact_mod_cast (ZMod.val_pos.mpr hj)
  have hkm : ((frequency χ j).val : ℝ) ≤ (m : ℝ) - 1 := by
    have h := (frequency χ j).val_lt
    have h' : (frequency χ j).val + 1 ≤ m := h
    have hreal : ((frequency χ j).val : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h'
    linarith
  have h := MeasureEquivalenceTrig.trig_coordinate_bound (m : ℝ)
    (frequency χ j).val (by exact_mod_cast hm) hk1 hkm
  simpa only [q, coordinateChar_frequency, zmod_frequency_one] using h

noncomputable def active (χ : AddChar (ι → ZMod m) ℂ) : Finset ι :=
  Finset.univ.filter fun j => frequency χ j ≠ 0

lemma long_multiplier_le (χ : AddChar (ι → ZMod m) ℂ) (a : ι → ZMod m) :
    (∑ j, ‖χ (axisHom j (a j)) - 1‖ ^ 2) ≤ 4 * ((active χ).card : ℝ) := by
  have hpoint (j : ι) : ‖χ (axisHom j (a j)) - 1‖ ^ 2 ≤
      if frequency χ j ≠ 0 then (4 : ℝ) else 0 := by
    by_cases hj : frequency χ j ≠ 0
    · rw [if_pos hj]
      have hnorm := norm_sub_le (χ (axisHom j (a j))) (1 : ℂ)
      simp only [χ.norm_apply, norm_one] at hnorm
      have hn := norm_nonneg (χ (axisHom j (a j)) - 1)
      nlinarith
    · rw [if_neg hj]
      have hz : frequency χ j = 0 := not_ne_iff.mp hj
      change ‖coordinateChar χ j (a j) - 1‖ ^ 2 ≤ 0
      rw [coordinateChar_frequency, hz]
      have hzmap : AddChar.zmodAddEquiv (0 : ZMod m) =
          (0 : AddChar (ZMod m) ℂ) :=
        map_zero (AddChar.zmodAddEquiv : ZMod m ≃+ AddChar (ZMod m) ℂ)
      rw [hzmap]
      simp
  calc
    (∑ j, ‖χ (axisHom j (a j)) - 1‖ ^ 2) ≤
        ∑ j, if frequency χ j ≠ 0 then (4 : ℝ) else 0 :=
      Finset.sum_le_sum fun j _ => hpoint j
    _ = 4 * ((active χ).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp [active, mul_comm]

theorem torus_multiplier (χ : AddChar (ι → ZMod m) ℂ) (a : ι → ZMod m)
    (hm : 2 ≤ m) (hn : Fintype.card ι ≤ m ^ 2) :
    (∑ j, ‖χ (axisHom j (a j)) - 1‖ ^ 2) ≤
      (4 * (m : ℝ) ^ 2 / (3 : ℝ) ^ Fintype.card ι) *
        ∑ ε : ι → Fin 3, ‖χ (shortShift ε) - 1‖ ^ 2 := by
  have hsub : active χ ⊆ Finset.univ := Finset.filter_subset _ _
  have hcard : (active χ).card ≤ m ^ 2 :=
    (Finset.card_le_card hsub).trans (by simpa using hn)
  have hscalar := MeasureEquivalenceScalar.square_scale_multiplier
    Finset.univ (active χ) (q χ) (m : ℝ) hsub
    (by exact_mod_cast (show 1 ≤ m by omega))
    (fun j _ => q_abs_le_one χ j)
    (fun j hj => q_abs_gap χ hm j (Finset.mem_filter.mp hj).2)
    (by exact_mod_cast hcard)
  calc
    (∑ j, ‖χ (axisHom j (a j)) - 1‖ ^ 2) ≤
        4 * ((active χ).card : ℝ) := long_multiplier_le χ a
    _ ≤ 4 * (m : ℝ) ^ 2 * (2 * (1 - ∏ j, q χ j)) := hscalar
    _ = (4 * (m : ℝ) ^ 2 / (3 : ℝ) ^ Fintype.card ι) *
        ∑ ε : ι → Fin 3, ‖χ (shortShift ε) - 1‖ ^ 2 := by
      rw [random_energy_multiplier]
      field_simp

/-- The finite-torus Hilbert inequality, with arbitrary shifts on each axis.
The missing common average over `x` cancels on both sides. -/
theorem finite_torus_hilbert {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (F : (ι → ZMod m) → E) (a : ι → ZMod m)
    (hm : 2 ≤ m) (hn : Fintype.card ι ≤ m ^ 2) :
    (∑ j, ∑ x, ‖F (x + axisHom j (a j)) - F x‖ ^ 2) ≤
      (4 * (m : ℝ) ^ 2 / (3 : ℝ) ^ Fintype.card ι) *
        ∑ ε : ι → Fin 3, ∑ x, ‖F (x + shortShift ε) - F x‖ ^ 2 :=
  MeasureEquivalenceFourier.spectral_comparison
    (fun j => axisHom j (a j)) shortShift _ (fun χ => torus_multiplier χ a hm hn) F

/-- The same inequality for arbitrary real inner product spaces. The finite
range spans a finite-dimensional subspace, whose orthonormal coordinates embed
isometrically into a complex Euclidean space. -/
theorem finite_torus_real_hilbert {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (F : (ι → ZMod m) → E) (a : ι → ZMod m)
    (hm : 2 ≤ m) (hn : Fintype.card ι ≤ m ^ 2) :
    (∑ j, ∑ x, ‖F (x + axisHom j (a j)) - F x‖ ^ 2) ≤
      (4 * (m : ℝ) ^ 2 / (3 : ℝ) ^ Fintype.card ι) *
        ∑ ε : ι → Fin 3, ∑ x, ‖F (x + shortShift ε) - F x‖ ^ 2 := by
  let S : Submodule ℝ E := Submodule.span ℝ (Set.range F)
  let : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range F)
  let f : (ι → ZMod m) → S := fun x =>
    ⟨F x, Submodule.subset_span (Set.mem_range_self x)⟩
  let b := stdOrthonormalBasis ℝ S
  let g : (ι → ZMod m) → EuclideanSpace ℂ (Fin (Module.finrank ℝ S)) :=
    fun x => WithLp.toLp 2 (fun i => ((b.repr (f x) i : ℝ) : ℂ))
  have hnorm (x y : ι → ZMod m) : ‖g x - g y‖ ^ 2 = ‖F x - F y‖ ^ 2 := by
    calc
      ‖g x - g y‖ ^ 2 = ‖b.repr (f x) - b.repr (f y)‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        apply Finset.sum_congr rfl
        intro i _
        simp [g, PiLp.sub_apply, ← Complex.ofReal_sub]
      _ = ‖f x - f y‖ ^ 2 := by rw [← map_sub, b.repr.norm_map]
      _ = ‖F x - F y‖ ^ 2 := rfl
  have h := finite_torus_hilbert g a hm hn
  simpa only [hnorm] using h

/-- Uniform-expectation form of the strengthened inequality. -/
theorem finite_torus_hilbert_expect {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (F : (ι → ZMod m) → E) (a : ι → ZMod m)
    (hm : 2 ≤ m) (hn : Fintype.card ι ≤ m ^ 2) :
    (∑ j, 𝔼 x, ‖F (x + axisHom j (a j)) - F x‖ ^ 2) ≤
      4 * (m : ℝ) ^ 2 *
        (𝔼 ε : ι → Fin 3, 𝔼 x, ‖F (x + shortShift ε) - F x‖ ^ 2) := by
  simp_rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_div, ← Finset.sum_div]
  have h := div_le_div_of_nonneg_right (finite_torus_hilbert F a hm hn)
    (Nat.cast_nonneg (Fintype.card (ι → ZMod m)) : (0 : ℝ) ≤ _)
  convert h using 1
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- Uniform-expectation form for real targets. -/
theorem finite_torus_real_hilbert_expect {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (F : (ι → ZMod m) → E) (a : ι → ZMod m)
    (hm : 2 ≤ m) (hn : Fintype.card ι ≤ m ^ 2) :
    (∑ j, 𝔼 x, ‖F (x + axisHom j (a j)) - F x‖ ^ 2) ≤
      4 * (m : ℝ) ^ 2 *
        (𝔼 ε : ι → Fin 3, 𝔼 x, ‖F (x + shortShift ε) - F x‖ ^ 2) := by
  simp_rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_div, ← Finset.sum_div]
  have h := div_le_div_of_nonneg_right (finite_torus_real_hilbert F a hm hn)
    (Nat.cast_nonneg (Fintype.card (ι → ZMod m)) : (0 : ℝ) ≤ _)
  convert h using 1
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- The original real-Hilbert half-turn inequality is an immediate instance.
No parity assumption is needed for the inequality; for even `m` this is the
half-turn of order two. -/
theorem half_turn_real_hilbert {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (F : (ι → ZMod m) → E)
    (hm : 2 ≤ m) (hn : Fintype.card ι ≤ m ^ 2) :
    (∑ j, 𝔼 x, ‖F (x + axisHom j ((m / 2 : ℕ) : ZMod m)) - F x‖ ^ 2) ≤
      4 * (m : ℝ) ^ 2 *
        (𝔼 ε : ι → Fin 3, 𝔼 x, ‖F (x + shortShift ε) - F x‖ ^ 2) :=
  finite_torus_real_hilbert_expect F (fun _ => ((m / 2 : ℕ) : ZMod m)) hm hn

end MeasureEquivalenceTorus
end Source48
end BenchmarkCountableProof

/- Whole source module: GridObstruction -/
namespace BenchmarkCountableProof
section Source49
/-! The dimension-uniform contradiction, including the two continuity
quantifiers. Actual circle-sequence grids are instantiated in a separate file. -/

open Filter Topology
open scoped Topology BigOperators

namespace MeasureEquivalenceGrid

open MeasureEquivalenceTorus

variable {H E : Type*} [NormedAddCommGroup H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Inverse continuity at the identity provides one bound for all long steps. -/
lemma inducing_long_bound (Ψ : H → E) (hΨ : IsInducing Ψ) :
    ∃ c > 0, ∀ h : H, (1 / 4 : ℝ) ≤ ‖h‖ → c ≤ ‖Ψ h - Ψ 0‖ := by
  have hball : Metric.ball (0 : H) (1 / 4) ∈ 𝓝 (0 : H) :=
    Metric.ball_mem_nhds _ (by norm_num)
  rw [hΨ.nhds_eq_comap 0, Filter.mem_comap] at hball
  obtain ⟨s, hs, hsub⟩ := hball
  obtain ⟨c, hc, hcs⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨c, hc, fun h hh => ?_⟩
  by_contra! hcontra
  have hm : h ∈ Metric.ball (0 : H) (1 / 4) :=
    hsub (hcs (by simpa [Metric.mem_ball, dist_eq_norm] using hcontra))
  have : ‖h‖ < (1 / 4 : ℝ) := by simpa [Metric.mem_ball, dist_eq_norm] using hm
  linarith

/-- One finite torus is already contradictory when the long steps all have
length at least c and all the short steps have length at most c/3. -/
theorem finite_grid_gap {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (F : (Fin (m ^ 2) → ZMod m) → E) (c : ℝ) (hc : 0 < c)
    (hlong : ∀ j x, c ≤
      ‖F (x + axisHom j ((m / 2 : ℕ) : ZMod m)) - F x‖)
    (hshort : ∀ ε x,
      ‖F (x + shortShift ε) - F x‖ ≤ c / 3) : False := by
  classical
  have hlow : (m : ℝ) ^ 2 * c ^ 2 ≤
      ∑ j : Fin (m ^ 2), 𝔼 x,
        ‖F (x + axisHom j ((m / 2 : ℕ) : ZMod m)) - F x‖ ^ 2 := by
    calc
      (m : ℝ) ^ 2 * c ^ 2 = ∑ _j : Fin (m ^ 2), 𝔼 _x : Fin (m ^ 2) → ZMod m,
          c ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => Finset.expect_le_expect fun x _ => by
        exact pow_le_pow_left₀ hc.le (hlong j x) 2
  have hupp : (𝔼 ε : Fin (m ^ 2) → Fin 3, 𝔼 x,
      ‖F (x + shortShift ε) - F x‖ ^ 2) ≤ (c / 3) ^ 2 := by
    calc
      _ ≤ (𝔼 _ε : Fin (m ^ 2) → Fin 3, 𝔼 _x : Fin (m ^ 2) → ZMod m,
          (c / 3) ^ 2) :=
        Finset.expect_le_expect fun ε _ => Finset.expect_le_expect fun x _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hshort ε x) 2
      _ = _ := by simp
  have htor := half_turn_real_hilbert F hm (by simp)
  have hbound : (m : ℝ) ^ 2 * c ^ 2 ≤ 4 * (m : ℝ) ^ 2 * (c / 3) ^ 2 :=
    hlow.trans (htor.trans (mul_le_mul_of_nonneg_left hupp (by positivity)))
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpos : 0 < (m : ℝ) ^ 2 * c ^ 2 := by positivity
  nlinarith

/-- An abstract grid criterion with the complete order of quantifiers.
The grid, modulus and dimension may depend on delta; the continuity constants
and long-step lower bound cannot depend on them. -/
theorem no_invariant_hilbert_embedding
    (hgrids : ∀ δ > 0, ∃ (m : ℕ) (_hm : 2 ≤ m)
      (grid : (Fin (m ^ 2) → ZMod m) →+ H),
      (∀ j, (1 / 4 : ℝ) ≤ ‖grid (axisHom j ((m / 2 : ℕ) : ZMod m))‖) ∧
      (∀ ε, ‖grid (shortShift ε)‖ < δ))
    (Ψ : H → E) (hΨ : IsEmbedding Ψ)
    (hinv : ∀ h k t, ‖Ψ (h + t) - Ψ (k + t)‖ = ‖Ψ h - Ψ k‖) : False := by
  obtain ⟨c, hc, hlong⟩ := inducing_long_bound Ψ hΨ.isInducing
  obtain ⟨δ, hδ, hsmall⟩ :=
    Metric.continuousAt_iff.mp (hΨ.continuous.continuousAt (x := 0)) (c / 3)
      (by positivity)
  obtain ⟨m, hm, grid, hgridlong, hgridshort⟩ := hgrids δ hδ
  letI : NeZero m := ⟨by omega⟩
  have hdisp (x y : Fin (m ^ 2) → ZMod m) :
      ‖Ψ (grid (x + y)) - Ψ (grid x)‖ = ‖Ψ (grid y) - Ψ 0‖ := by
    rw [map_add, add_comm (grid x) (grid y)]
    simpa only [zero_add] using hinv (grid y) 0 (grid x)
  apply finite_grid_gap hm (Ψ ∘ grid) c hc
  · intro j x
    simpa only [Function.comp_apply, hdisp] using hlong _ (hgridlong j)
  · intro ε x
    rw [Function.comp_apply, Function.comp_apply, hdisp]
    apply le_of_lt
    simpa only [dist_eq_norm] using hsmall
      (show dist (grid (shortShift ε)) 0 < δ by simpa using hgridshort ε)

end MeasureEquivalenceGrid
end Source49
end BenchmarkCountableProof

/- Whole source module: CircleGrids -/
namespace BenchmarkCountableProof
section Source50
open Filter Topology
open scoped Topology BigOperators ENNReal NNReal

noncomputable section

namespace MeasureEquivalenceCircle

open MeasureEquivalenceTorus MeasureEquivalenceGrid

abbrev Hp (p : ℝ≥0∞) := lp (fun _ : ℕ => UnitAddCircle) p

variable (p : ℝ≥0∞) {m n : ℕ} [NeZero m]

def gridValue (x : Fin n → ZMod m) (k : ℕ) : UnitAddCircle :=
  if hk : k < n then ZMod.toAddCircle (x ⟨k, hk⟩) else 0

def grid : (Fin n → ZMod m) →+ Hp p where
  toFun x := ⟨gridValue x, (memℓp_zero (by
    apply (Finset.finite_toSet (Finset.range n)).subset
    intro k hk
    by_contra hkn
    have : ¬ k < n := by simpa using hkn
    exact hk (by simp [gridValue, this]))).of_exponent_ge (by positivity)⟩
  map_zero' := by
    apply lp.ext
    funext k
    change gridValue (0 : Fin n → ZMod m) k = (0 : UnitAddCircle)
    simp [gridValue]
  map_add' x y := by
    ext k
    change gridValue (x + y) k = gridValue x k + gridValue y k
    simp only [gridValue]
    split_ifs <;> simp

@[simp] lemma grid_apply (x : Fin n → ZMod m) (k : ℕ) :
    grid p x k = gridValue x k := rfl

lemma grid_apply_fin (x : Fin n → ZMod m) (j : Fin n) :
    grid p x j = ZMod.toAddCircle (x j) := by simp [gridValue]

lemma grid_apply_ge (x : Fin n → ZMod m) {k : ℕ} (hk : n ≤ k) :
    grid p x k = 0 := by simp [gridValue, not_lt.mpr hk]

lemma circle_step_bound (t : Fin 3) :
    ‖ZMod.toAddCircle (step (m := m) t)‖ ≤ 1 / (m : ℝ) := by
  have hbase : ‖((1 / (m : ℝ) : ℝ) : UnitAddCircle)‖ ≤ 1 / (m : ℝ) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (m : ℝ))]
      using (QuotientAddGroup.norm_mk_le_norm
        (m := (1 / (m : ℝ) : ℝ)) (S := AddSubgroup.zmultiples (1 : ℝ)))
  have hone : ZMod.toAddCircle (1 : ZMod m) = ((1 / (m : ℝ) : ℝ) : UnitAddCircle) := by
    simpa using ZMod.toAddCircle_natCast (N := m) 1
  fin_cases t <;> simp [step, map_neg, hone] <;> simpa [one_div] using hbase

lemma half_turn_value (heven : Even m) :
    ZMod.toAddCircle ((m / 2 : ℕ) : ZMod m) = ((1 / 2 : ℝ) : UnitAddCircle) := by
  rw [ZMod.toAddCircle_natCast]
  congr 1
  have hmul : m / 2 * 2 = m := Nat.div_mul_cancel heven.two_dvd
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hreal : (m / 2 : ℕ) * (2 : ℝ) = m := by exact_mod_cast hmul
  apply (div_eq_iff hm).mpr
  linarith

lemma grid_long_bound (hp : p ≠ 0) (heven : Even m) (j : Fin n) :
    (1 / 4 : ℝ) ≤ ‖grid p (axisHom j ((m / 2 : ℕ) : ZMod m))‖ := by
  have h := lp.norm_apply_le_norm hp (grid p (axisHom j ((m / 2 : ℕ) : ZMod m))) j
  rw [grid_apply_fin] at h
  simp only [axisHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ite_true] at h
  rw [half_turn_value heven] at h
  have hnorm : ‖((1 / 2 : ℝ) : UnitAddCircle)‖ = (1 / 2 : ℝ) := by
    simpa using AddCircle.norm_half_period_eq (1 : ℝ)
  rw [hnorm] at h
  exact (show (1 / 4 : ℝ) ≤ 1 / 2 by norm_num).trans h

lemma grid_short_coordinate (ε : Fin n → Fin 3) (k : ℕ) :
    ‖grid (m := m) p (shortShift ε) k‖ ≤ 1 / (m : ℝ) := by
  by_cases hk : k < n
  · simpa [gridValue, hk, shortShift] using circle_step_bound (m := m) (ε ⟨k, hk⟩)
  · simp [gridValue, hk]

lemma grid_short_sup (ε : Fin n → Fin 3) :
    ‖grid (m := m) ⊤ (shortShift ε)‖ ≤ 1 / (m : ℝ) :=
  lp.norm_le_of_forall_le (by positivity) (grid_short_coordinate ⊤ ε)

lemma grid_norm_rpow (hp : 0 < p.toReal) (x : Fin n → ZMod m) :
    ‖grid p x‖ ^ p.toReal = ∑ k ∈ Finset.range n, ‖grid p x k‖ ^ p.toReal := by
  rw [lp.norm_rpow_eq_tsum hp]
  apply tsum_eq_sum
  intro k hk
  rw [grid_apply_ge p x (by simpa using hk), norm_zero, Real.zero_rpow hp.ne']

lemma grid_short_rpow (hp : 0 < p.toReal) (ε : Fin n → Fin 3) :
    ‖grid (m := m) p (shortShift ε)‖ ^ p.toReal ≤
      (n : ℝ) * (1 / (m : ℝ)) ^ p.toReal := by
  rw [grid_norm_rpow p hp]
  calc
    _ ≤ ∑ _k ∈ Finset.range n, (1 / (m : ℝ)) ^ p.toReal :=
      Finset.sum_le_sum fun k _ => Real.rpow_le_rpow (norm_nonneg _)
        (grid_short_coordinate p ε k) hp.le
    _ = _ := by simp

lemma grid_square_short_rpow (hp : 0 < p.toReal) (ε : Fin (m ^ 2) → Fin 3) :
    ‖grid (m := m) p (shortShift ε)‖ ^ p.toReal ≤ (m : ℝ) ^ (2 - p.toReal) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (NeZero.pos m)
  convert grid_short_rpow p hp ε using 1
  rw [Real.rpow_sub hm, Real.rpow_two]
  simp [Nat.cast_pow, one_div, Real.inv_rpow, div_eq_mul_inv]

/-- Even moduli can be chosen arbitrarily far out; the dimension is then m². -/
lemma exists_even_rpow_small {r δ : ℝ} (hr : r < 0) (hδ : 0 < δ) :
    ∃ m : ℕ, 2 ≤ m ∧ Even m ∧ (m : ℝ) ^ r < δ := by
  have ht : Tendsto (fun m : ℕ => (m : ℝ) ^ r) atTop (𝓝 0) := by
    simpa only [neg_neg, Function.comp_def] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hr)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have he : ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ r < δ := ht.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨2 * (N + 1), by omega, ⟨N + 1, by omega⟩, hN _ (by omega)⟩

/-- The circle null-sequence group, with the inherited supremum norm. -/
def H0subgroup : AddSubgroup (Hp ⊤) where
  carrier := {x | Tendsto (fun k => x k) atTop (𝓝 0)}
  zero_mem' := by simpa using tendsto_const_nhds
  add_mem' hx hy := by simpa using hx.add hy
  neg_mem' hx := by simpa using hx.neg

abbrev H0 := H0subgroup

lemma grid_null (x : Fin n → ZMod m) : grid ⊤ x ∈ H0subgroup := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with k hk
  exact (grid_apply_ge ⊤ x hk).symm

def grid0 : (Fin n → ZMod m) →+ H0 :=
  (grid ⊤).codRestrict H0subgroup grid_null

lemma grid0_long_bound (heven : Even m) (j : Fin n) :
    (1 / 4 : ℝ) ≤ ‖grid0 (axisHom j ((m / 2 : ℕ) : ZMod m))‖ :=
  grid_long_bound ⊤ (by simp) heven j

lemma grid0_short_bound (ε : Fin n → Fin 3) :
    ‖grid0 (m := m) (shortShift ε)‖ ≤ 1 / (m : ℝ) := grid_short_sup ε

theorem H0_has_small_grids : ∀ δ > 0, ∃ (m : ℕ) (_hm : 2 ≤ m)
    (g : (Fin (m ^ 2) → ZMod m) →+ H0),
    (∀ j, (1 / 4 : ℝ) ≤ ‖g (axisHom j ((m / 2 : ℕ) : ZMod m))‖) ∧
    (∀ ε, ‖g (shortShift ε)‖ < δ) := by
  intro δ hδ
  obtain ⟨m, hm, heven, hsmall⟩ := exists_even_rpow_small (r := -1) (by norm_num) hδ
  letI : NeZero m := ⟨by omega⟩
  refine ⟨m, hm, grid0, grid0_long_bound heven, fun ε => ?_⟩
  apply (grid0_short_bound ε).trans_lt
  simpa [Real.rpow_neg_one, one_div] using hsmall

theorem Hp_has_small_grids [Fact (1 ≤ p)] (hp : 2 < p.toReal) :
    ∀ δ > 0, ∃ (m : ℕ) (_hm : 2 ≤ m)
      (g : (Fin (m ^ 2) → ZMod m) →+ Hp p),
      (∀ j, (1 / 4 : ℝ) ≤ ‖g (axisHom j ((m / 2 : ℕ) : ZMod m))‖) ∧
      (∀ ε, ‖g (shortShift ε)‖ < δ) := by
  intro δ hδ
  have hp0 : 0 < p.toReal := by linarith
  have hpn : p ≠ 0 := by intro hz; norm_num [hz] at hp
  obtain ⟨m, hm, heven, hsmall⟩ := exists_even_rpow_small
    (r := 2 - p.toReal) (by linarith) (Real.rpow_pos_of_pos hδ p.toReal)
  letI : NeZero m := ⟨by omega⟩
  refine ⟨m, hm, grid p, grid_long_bound p hpn heven, fun ε => ?_⟩
  exact (Real.rpow_lt_rpow_iff (norm_nonneg _) hδ.le hp0).mp
    ((grid_square_short_rpow p hp0 ε).trans_lt hsmall)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Concrete null-circle-sequence obstruction, with no grid assumptions. -/
theorem no_H0_invariant_hilbert_embedding (Ψ : H0 → E) (hΨ : IsEmbedding Ψ)
    (hinv : ∀ h k t, ‖Ψ (h + t) - Ψ (k + t)‖ = ‖Ψ h - Ψ k‖) : False :=
  no_invariant_hilbert_embedding H0_has_small_grids Ψ hΨ hinv

/-- Concrete finite-p circle-sequence obstruction. `2 < p.toReal` excludes
the infinite exponent, and `[Fact (1 ≤ p)]` supplies its standard lp metric. -/
theorem no_Hp_invariant_hilbert_embedding [Fact (1 ≤ p)] (hp : 2 < p.toReal)
    (Ψ : Hp p → E) (hΨ : IsEmbedding Ψ)
    (hinv : ∀ h k t, ‖Ψ (h + t) - Ψ (k + t)‖ = ‖Ψ h - Ψ k‖) : False :=
  no_invariant_hilbert_embedding (Hp_has_small_grids p hp) Ψ hΨ hinv

end MeasureEquivalenceCircle
end
end Source50
end BenchmarkCountableProof

/- Whole source module: CircleTopology -/
namespace BenchmarkCountableProof
section Source51
open Filter Topology Set TopologicalSpace
open scoped Topology BigOperators ENNReal NNReal

noncomputable section

namespace MeasureEquivalenceCircleTopology

open MeasureEquivalenceCircle

abbrev K := ℕ → UnitAddCircle

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

def trunc (s : Finset ℕ) (x : K) : Hp p :=
  ∑ i ∈ s, lp.single p i (x i)

lemma continuous_trunc (s : Finset ℕ) : Continuous (trunc p s) := by
  apply continuous_finsetSum
  intro i hi
  exact (lp.singleContinuousAddMonoidHom (fun _ : ℕ => UnitAddCircle) p i).continuous.comp
    (continuous_apply i)

lemma dense_trunc (hp : p ≠ ⊤) : Dense (⋃ s : Finset ℕ, range (trunc p s)) := by
  intro x
  have hx := lp.hasSum_single hp x
  apply mem_closure_of_tendsto hx
  exact Filter.Eventually.of_forall (fun s => mem_iUnion.mpr ⟨s, ⟨(x : K), rfl⟩⟩)

theorem hp_separable (hp : p ≠ ⊤) : SeparableSpace (Hp p) := by
  apply (dense_trunc p hp).isSeparable_iff.mp
  exact IsSeparable.iUnion (fun s => isSeparable_range (continuous_trunc p s))

lemma continuous_hp_coordinates : Continuous (fun h : Hp p => (h : K)) := by
  apply continuous_pi
  intro i
  exact (lp.lipschitzWith_one_eval p i).continuous

theorem hp_polish (hp : p ≠ ⊤) : PolishSpace (Hp p) := by
  let := hp_separable p hp
  infer_instance

lemma h0_closed : IsClosed (H0subgroup : Set (Hp ⊤)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u x hu hx
  change Tendsto (fun k => x k) atTop (𝓝 0)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := (Metric.tendsto_nhds.mp hx (ε / 2) (by positivity)).exists
  have huj : Tendsto (fun k => u j k) atTop (𝓝 0) := hu j
  filter_upwards [Metric.tendsto_nhds.mp huj (ε / 2) (by positivity)] with k hk
  have hcoord : dist (x k) (u j k) ≤ dist x (u j) := by
    simpa only [dist_eq_norm, lp.coeFn_sub, Pi.sub_apply] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero (x - u j) k
  calc
    dist (x k) 0 ≤ dist (x k) (u j k) + dist (u j k) 0 := dist_triangle _ _ _
    _ ≤ dist x (u j) + dist (u j k) 0 := add_le_add hcoord le_rfl
    _ < ε := by rw [dist_comm x]; linarith

theorem h0_complete : CompleteSpace H0 := h0_closed.isComplete.completeSpace_coe

omit [Fact (1 ≤ p)] in
lemma trunc_apply (s : Finset ℕ) (x : K) (k : ℕ) :
    trunc p s x k = if k ∈ s then x k else 0 := by
  simp only [trunc, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single]

lemma trunc_null (s : Finset ℕ) (x : K) : trunc ⊤ s x ∈ H0subgroup := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (s.sup id)] with k hk
  have hkn : k ∉ s := by
    intro hmem
    have : k ≤ s.sup id := Finset.le_sup (f := id) hmem
    omega
  simp [trunc_apply, hkn]

def trunc0 (s : Finset ℕ) (x : K) : H0 := ⟨trunc ⊤ s x, trunc_null s x⟩

lemma continuous_trunc0 (s : Finset ℕ) : Continuous (trunc0 s) :=
  (continuous_trunc ⊤ s).subtype_mk _

lemma tendsto_trunc0 (x : H0) :
    Tendsto (fun N : ℕ => trunc0 (Finset.range N) ((x : Hp ⊤) : K)) atTop (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hx : Tendsto (fun k => (x : Hp ⊤) k) atTop (𝓝 0) := x.property
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Metric.tendsto_nhds.mp hx (ε / 2) (by positivity))
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (b := ε / 2) _ (by linarith)
  change ‖trunc ⊤ (Finset.range n) ((x : Hp ⊤) : K) - (x : Hp ⊤)‖ ≤ ε / 2
  apply lp.norm_le_of_forall_le (by positivity)
  intro k
  simp only [lp.coeFn_sub, Pi.sub_apply, trunc_apply, Finset.mem_range]
  split_ifs with hk
  · simp; positivity
  · have hNk : N ≤ k := by omega
    simpa only [zero_sub, norm_neg, dist_zero_right] using (hN k hNk).le

lemma dense_trunc0 : Dense (⋃ s : Finset ℕ, range (trunc0 s)) := by
  intro x
  apply mem_closure_of_tendsto (tendsto_trunc0 x)
  exact Filter.Eventually.of_forall (fun N =>
    mem_iUnion.mpr ⟨Finset.range N, ⟨((x : Hp ⊤) : K), rfl⟩⟩)

theorem h0_separable : SeparableSpace H0 := by
  apply dense_trunc0.isSeparable_iff.mp
  exact IsSeparable.iUnion (fun s => isSeparable_range (continuous_trunc0 s))

theorem h0_polish : PolishSpace H0 := by
  let := h0_complete
  let := h0_separable
  infer_instance

lemma continuous_h0_coordinates : Continuous (fun h : H0 => ((h : Hp ⊤) : K)) :=
  (continuous_hp_coordinates ⊤).comp continuous_subtype_val

end MeasureEquivalenceCircleTopology
end
end Source51
end BenchmarkCountableProof

/- Whole source module: CircleRowCover -/
namespace BenchmarkCountableProof
section Source52
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

open MeasureEquivalenceCircle MeasureEquivalenceCircleTopology

abbrev NullCircleGroup := H0

local instance : PolishSpace NullCircleGroup := h0_polish
local instance : SeparableSpace NullCircleGroup := h0_separable
local instance : MeasurableSpace NullCircleGroup := borel NullCircleGroup
local instance : BorelSpace NullCircleGroup := ⟨rfl⟩
local instance : MeasurableSpace CircleSequences := borel CircleSequences
local instance : BorelSpace CircleSequences := ⟨rfl⟩

def nullCircleCoordinates (h : NullCircleGroup) : CircleSequences :=
  ((h : Hp ⊤) : CircleSequences)

theorem continuous_nullCircleCoordinates : Continuous nullCircleCoordinates :=
  continuous_h0_coordinates

def circleAction (p : CircleSequences × NullCircleGroup) : CircleSequences :=
  p.1 + nullCircleCoordinates p.2

theorem continuous_circleAction : Continuous circleAction :=
  continuous_fst.add (continuous_nullCircleCoordinates.comp continuous_snd)

/-- Endpoint maps of the actual circle null-group action are open. -/
theorem isOpenMap_circleAction : IsOpenMap circleAction := by
  intro W hW
  have heq : circleAction '' W = ⋃ h : NullCircleGroup,
      (fun x : CircleSequences => x + nullCircleCoordinates h) ''
        {x | (x, h) ∈ W} := by
    ext y
    constructor
    · rintro ⟨⟨x, h⟩, hxh, rfl⟩
      exact mem_iUnion.mpr ⟨h, x, hxh, rfl⟩
    · intro hy
      obtain ⟨h, x, hxh, hxy⟩ := mem_iUnion.mp hy
      exact ⟨(x, h), hxh, hxy⟩
  rw [heq]
  apply isOpen_iUnion
  intro h
  exact isOpenMap_add_right (nullCircleCoordinates h) _
    (hW.preimage (continuous_id.prodMk continuous_const))

theorem circleAction_null_related (p : CircleSequences × NullCircleGroup) :
    CircleNullDifference p.1 (circleAction p) := by
  have hh : Tendsto (fun n => nullCircleCoordinates p.2 n) atTop (𝓝 0) := p.2.property
  simpa [CircleNullDifference, MeasureEquivalenceCircleReduction.CircleNullRel,
    circleAction, nullCircleCoordinates] using hh.neg

/-- The concrete Baire cover step of the c0 jump proof: on one nonempty
rectangle a fixed output row matches a fixed input row with one uniform bound. -/
theorem circle_row_match_rectangle
    (F : CircleSequences → ℕ → RealSequences) (hFm : Measurable F)
    (hF : Homomorphism CircleNullDifference (Jump BoundedDifference) F)
    (k : ℕ) (A : Set CircleSequences) (hAo : IsOpen A) (hAn : A.Nonempty) :
    ∃ l n : ℕ, ∃ U : Set CircleSequences, ∃ W : Set NullCircleGroup,
      IsOpen U ∧ U.Nonempty ∧ IsOpen W ∧ W.Nonempty ∧
      U ×ˢ W ⊆ circleAction ⁻¹' A ∧
      ∀ᶠ p in residual (CircleSequences × NullCircleGroup),
        p ∈ U ×ˢ W → UniformBound n (F (circleAction p) k) (F p.1 l) := by
  classical
  let B : ℕ × ℕ → Set (CircleSequences × NullCircleGroup) := fun i =>
    {p | UniformBound i.2 (F (circleAction p) k) (F p.1 i.1)}
  have hB (i : ℕ × ℕ) : BaireMeasurableSet (B i) := by
    apply MeasurableSet.baireMeasurableSet
    exact (isClosed_uniformBound i.2).measurableSet.preimage
      (((measurable_pi_apply k).comp (hFm.comp continuous_circleAction.measurable)).prodMk
        ((measurable_pi_apply i.1).comp (hFm.comp measurable_fst)))
  let Ω : Set (CircleSequences × NullCircleGroup) := circleAction ⁻¹' A
  have hΩo : IsOpen Ω := hAo.preimage continuous_circleAction
  have hΩn : Ω.Nonempty := by
    obtain ⟨x, hx⟩ := hAn
    refine ⟨(x, 0), ?_⟩
    have heq : circleAction (x, 0) = x := by
      ext n
      change x n + 0 = x n
      exact add_zero _
    change circleAction (x, 0) ∈ A
    rw [heq]
    exact hx
  have hCover : Ω ⊆ ⋃ i, B i := by
    intro p _hp
    obtain ⟨l, hl⟩ := (hF p.1 (circleAction p) (circleAction_null_related p)).2 k
    obtain ⟨n, hn⟩ := boundedDifference_equivalence.symm hl
    exact mem_iUnion.mpr ⟨(l, n), hn⟩
  obtain ⟨i, V, hVo, hVn, hVΩ, hVres⟩ :=
    baire_cover_local_residual B hB Ω hΩo hΩn hCover
  obtain ⟨⟨x, h⟩, hxh⟩ := hVn
  obtain ⟨U, W, hUo, hWo, hxU, hhW, hUW⟩ := isOpen_prod_iff.mp hVo x h hxh
  refine ⟨i.1, i.2, U, W, hUo, ⟨x, hxU⟩, hWo, ⟨h, hhW⟩,
    hUW.trans hVΩ, ?_⟩
  filter_upwards [hVres] with p hp hpUW
  exact hp (hUW hpUW)




end BenchmarkJump
end
end Source52
end BenchmarkCountableProof

/- Whole source module: CircleSmallPairs -/
namespace BenchmarkCountableProof
section Source53
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

open MeasureEquivalenceCircle MeasureEquivalenceCircleTopology

local instance : PolishSpace NullCircleGroup := h0_polish
local instance : SeparableSpace NullCircleGroup := h0_separable

abbrev CircleTriples := CircleSequences × (NullCircleGroup × NullCircleGroup)

def tripleFirst (t : CircleTriples) : CircleSequences × NullCircleGroup :=
  (t.1, t.2.1)

def tripleSecond (t : CircleTriples) : CircleSequences × NullCircleGroup :=
  (t.1, t.2.2)

def tripleEndpoints (t : CircleTriples) : CircleSequences × CircleSequences :=
  (circleAction (tripleFirst t), circleAction (tripleSecond t))

theorem continuous_tripleFirst : Continuous tripleFirst :=
  continuous_fst.prodMk (continuous_fst.comp continuous_snd)

theorem continuous_tripleSecond : Continuous tripleSecond :=
  continuous_fst.prodMk (continuous_snd.comp continuous_snd)

theorem isOpenMap_tripleFirst : IsOpenMap tripleFirst :=
  IsOpenMap.id.prodMap isOpenMap_fst

theorem isOpenMap_tripleSecond : IsOpenMap tripleSecond :=
  IsOpenMap.id.prodMap isOpenMap_snd

theorem continuous_tripleEndpoints : Continuous tripleEndpoints :=
  (continuous_circleAction.comp continuous_tripleFirst).prodMk
    (continuous_circleAction.comp continuous_tripleSecond)

/-- The two row matches imply a uniform same-row bound for a comeager set
of triples, while both endpoints may additionally be required in D. -/
theorem circle_good_triples
    (U : Set CircleSequences) (W : Set NullCircleGroup) (D : Set CircleSequences)
    (hD : D ∈ residual CircleSequences) (f g : CircleSequences → RealSequences)
    (n : ℕ)
    (hRes : ∀ᶠ p in residual (CircleSequences × NullCircleGroup),
      p ∈ U ×ˢ W → UniformBound n (f (circleAction p)) (g p.1)) :
    ∀ᶠ t in residual CircleTriples,
      t ∈ U ×ˢ (W ×ˢ W) →
        tripleEndpoints t ∈ D ×ˢ D ∧
        UniformBound (2 * n) (f (tripleEndpoints t).1) (f (tripleEndpoints t).2) := by
  have h1 := tendsto_residual_of_isOpenMap continuous_tripleFirst isOpenMap_tripleFirst hRes
  have h2 := tendsto_residual_of_isOpenMap continuous_tripleSecond isOpenMap_tripleSecond hRes
  have hD1 := tendsto_residual_of_isOpenMap
    (continuous_circleAction.comp continuous_tripleFirst)
    (isOpenMap_circleAction.comp isOpenMap_tripleFirst) hD
  have hD2 := tendsto_residual_of_isOpenMap
    (continuous_circleAction.comp continuous_tripleSecond)
    (isOpenMap_circleAction.comp isOpenMap_tripleSecond) hD
  filter_upwards [h1, h2, hD1, hD2] with t ht1 ht2 htD1 htD2 htRect
  refine ⟨⟨htD1, htD2⟩, ?_⟩
  have hB1 := ht1 ⟨htRect.1, htRect.2.1⟩
  have hB2 := ht2 ⟨htRect.1, htRect.2.2⟩
  have hB := uniformBound_trans hB1 (uniformBound_symm hB2)
  simpa only [two_mul] using hB

theorem mem_closure_inter_of_residual {T : Type*} [TopologicalSpace T] [BaireSpace T]
    (O G : Set T) (hOo : IsOpen O) (hG : G ∈ residual T) :
    O ⊆ closure (O ∩ G) := by
  intro x hx
  apply mem_closure_iff.mpr
  intro V hVo hxV
  obtain ⟨y, ⟨hyV, hyO⟩, hyG⟩ :=
    (dense_of_mem_residual hG).inter_open_nonempty (V ∩ O) (hVo.inter hOo) ⟨x, hxV, hx⟩
  exact ⟨y, hyV, hyO, hyG⟩

/-- Closed uniform output bounds extend along limits of pairs inside the
relative continuity set, exactly as used by the manuscript's closure step. -/
theorem uniformBound_of_mem_closure {D : Set CircleSequences}
    (f : CircleSequences → RealSequences) (hf : ContinuousOn f D)
    (n : ℕ) (S : Set (CircleSequences × CircleSequences))
    (hSD : S ⊆ D ×ˢ D)
    (hBound : ∀ p ∈ S, UniformBound n (f p.1) (f p.2))
    (p : CircleSequences × CircleSequences) (hpD : p ∈ D ×ˢ D)
    (hp : p ∈ closure S) : UniformBound n (f p.1) (f p.2) := by
  have hc := ((hf p.1 hpD.1).prodMap (hf p.2 hpD.2)).mono hSD
  have hm : MapsTo (Prod.map f f) S
      {q : RealSequences × RealSequences | UniformBound n q.1 q.2} := hBound
  have hcl := hc.mem_closure hp hm
  simpa only [(isClosed_uniformBound n).closure_eq] using hcl

theorem norm_trunc0_le (s : Finset ℕ) (t : CircleSequences) (δ : ℝ)
    (hδ : 0 ≤ δ) (ht : ∀ i, ‖t i‖ ≤ δ) :
    ‖trunc0 s t‖ ≤ δ := by
  change ‖trunc ⊤ s t‖ ≤ δ
  apply lp.norm_le_of_forall_le hδ
  intro i
  rw [trunc_apply]
  split_ifs
  · exact ht i
  · simpa using hδ

theorem nullCircleCoordinates_add (h₁ h₂ : NullCircleGroup) :
    nullCircleCoordinates (h₁ + h₂) = nullCircleCoordinates h₁ + nullCircleCoordinates h₂ := rfl

theorem tendsto_truncated_endpoint (x y : CircleSequences) (h₀ : NullCircleGroup) :
    Tendsto
      (fun N : ℕ => circleAction
        (x, h₀ + trunc0 (Finset.range N) (y - circleAction (x, h₀))))
      atTop (𝓝 y) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop i] with N hN
  change y i = x i + (nullCircleCoordinates h₀ i +
    trunc ⊤ (Finset.range N) (y - circleAction (x, h₀)) i)
  rw [trunc_apply]
  simp only [Finset.mem_range, hN, ite_true, Pi.sub_apply, circleAction, Pi.add_apply,
    nullCircleCoordinates]
  abel





end BenchmarkJump
end
end Source53
end BenchmarkCountableProof

/- Whole source module: CircleRowClosure -/
namespace BenchmarkCountableProof
section Source54
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

open MeasureEquivalenceCircle MeasureEquivalenceCircleTopology

local instance : PolishSpace NullCircleGroup := h0_polish
local instance : SeparableSpace NullCircleGroup := h0_separable

/-- The finite-truncation closure step in the concrete circle proof.
The uniform output bound holds even for a pair whose difference need not
itself be a null sequence, provided the coordinate distances are small. -/
theorem circle_small_pair_bound
    (U : Set CircleSequences) (W : Set NullCircleGroup)
    (hUo : IsOpen U) (hWo : IsOpen W)
    (D : Set CircleSequences) (hD : D ∈ residual CircleSequences)
    (f g : CircleSequences → RealSequences) (hf : ContinuousOn f D)
    (n : ℕ)
    (hRes : ∀ᶠ p in residual (CircleSequences × NullCircleGroup),
      p ∈ U ×ˢ W → UniformBound n (f (circleAction p)) (g p.1))
    (h₀ : NullCircleGroup) (hh₀ : h₀ ∈ W) (ε : ℝ)
    (hBall : Metric.ball h₀ ε ⊆ W)
    (x z : CircleSequences) (hx : x ∈ U)
    (hyD : circleAction (x, h₀) ∈ D) (hzD : z ∈ D)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδε : δ < ε)
    (hSmall : ∀ i, ‖z i - circleAction (x, h₀) i‖ ≤ δ) :
    UniformBound (2 * n) (f (circleAction (x, h₀))) (f z) := by
  classical
  let Ω : Set CircleTriples := U ×ˢ (W ×ˢ W)
  let G : Set CircleTriples := {t | t ∈ Ω →
    tripleEndpoints t ∈ D ×ˢ D ∧
    UniformBound (2 * n) (f (tripleEndpoints t).1) (f (tripleEndpoints t).2)}
  have hG : G ∈ residual CircleTriples := circle_good_triples U W D hD f g n hRes
  let S : Set CircleTriples := Ω ∩ G
  have hΩclosure : Ω ⊆ closure S :=
    mem_closure_inter_of_residual Ω G (hUo.prod (hWo.prod hWo)) hG
  let v : ℕ → CircleTriples := fun N =>
    (x, h₀, h₀ + trunc0 (Finset.range N) (z - circleAction (x, h₀)))
  have hv (N : ℕ) : v N ∈ Ω := by
    refine ⟨hx, hh₀, hBall ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have ht := norm_trunc0_le (Finset.range N) (z - circleAction (x, h₀)) δ hδ hSmall
    simpa only [v, add_sub_cancel_left] using lt_of_le_of_lt ht hδε
  have hvImg (N : ℕ) : tripleEndpoints (v N) ∈ closure (tripleEndpoints '' S) :=
    image_closure_subset_closure_image continuous_tripleEndpoints
      ⟨v N, hΩclosure (hv N), rfl⟩
  have hvLim : Tendsto (fun N => tripleEndpoints (v N)) atTop
      (𝓝 (circleAction (x, h₀), z)) :=
    tendsto_const_nhds.prodMk_nhds (tendsto_truncated_endpoint x z h₀)
  have hp : (circleAction (x, h₀), z) ∈ closure (tripleEndpoints '' S) :=
    isClosed_closure.mem_of_tendsto hvLim (Eventually.of_forall hvImg)
  apply uniformBound_of_mem_closure f hf (2 * n) (tripleEndpoints '' S)
    (fun p hp => ?_) (fun p hp => ?_) (circleAction (x, h₀), z) ⟨hyD, hzD⟩ hp
  · obtain ⟨t, ht, rfl⟩ := hp
    exact (ht.2 ht.1).1
  · obtain ⟨t, ht, rfl⟩ := hp
    exact (ht.2 ht.1).2



end BenchmarkJump
end
end Source54
end BenchmarkCountableProof

/- Whole source module: CircleChart -/
namespace BenchmarkCountableProof
section Source55
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

abbrev CircleChartInterval := Set.Ioo (0 : ℝ) 1
abbrev CircleChartSpace := ℕ → CircleChartInterval

def circleChartCoordinate (x : CircleChartInterval) : UnitAddCircle := (x : ℝ)

def circleChart (x : CircleChartSpace) : CircleSequences :=
  fun i => circleChartCoordinate (x i)

theorem isOpenEmbedding_circleChartCoordinate : IsOpenEmbedding circleChartCoordinate := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
  · intro x y hxy
    apply Subtype.ext
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show (x : ℝ) ∈ Ico (0 : ℝ) (0 + 1) from by
        simpa only [zero_add] using Ioo_subset_Ico_self x.property)
      (show (y : ℝ) ∈ Ico (0 : ℝ) (0 + 1) from by
        simpa only [zero_add] using Ioo_subset_Ico_self y.property)).mp
    exact hxy
  · exact QuotientAddGroup.isOpenMap_coe.comp isOpen_Ioo.isOpenMap_subtype_val

theorem isEmbedding_circleChart : IsEmbedding circleChart :=
  IsEmbedding.piMap (fun _ => isOpenEmbedding_circleChartCoordinate.isEmbedding)

theorem continuous_circleChart : Continuous circleChart := isEmbedding_circleChart.continuous

theorem range_circleChartCoordinate : range circleChartCoordinate = ({0}ᶜ : Set UnitAddCircle) := by
  have hr := (AddCircle.openPartialHomeomorphCoe (1 : ℝ) 0).image_source_eq_target
  convert hr using 1
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, by simpa [AddCircle.openPartialHomeomorphCoe, CircleChartInterval]
        using x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, by simpa [AddCircle.openPartialHomeomorphCoe, CircleChartInterval] using hx⟩, rfl⟩

theorem denseRange_circleChartCoordinate : DenseRange circleChartCoordinate := by
  intro y
  by_cases hy : y = 0
  · subst y
    have h0 : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
      rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
      exact ⟨le_rfl, by norm_num⟩
    have hcl := image_closure_subset_closure_image (AddCircle.continuous_mk' (1 : ℝ))
      ⟨0, h0, rfl⟩
    have heq : ((fun x : ℝ => (x : UnitAddCircle)) '' Set.Ioo (0 : ℝ) 1) =
        range circleChartCoordinate := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.property, rfl⟩
    change (0 : UnitAddCircle) ∈ closure
      ((fun x : ℝ => (x : UnitAddCircle)) '' Set.Ioo (0 : ℝ) 1) at hcl
    rw [heq] at hcl
    exact hcl
  · apply subset_closure
    rw [range_circleChartCoordinate]
    simpa using hy

theorem denseRange_circleChart : DenseRange circleChart :=
  DenseRange.piMap (fun _ => denseRange_circleChartCoordinate)

theorem range_circleChart : range circleChart = {x : CircleSequences | ∀ i, x i ≠ 0} := by
  classical
  ext x
  constructor
  · rintro ⟨y, rfl⟩ i
    have hi : circleChartCoordinate (y i) ∈ range circleChartCoordinate := mem_range_self _
    rw [range_circleChartCoordinate] at hi
    exact hi
  · intro hx
    have hi (i : ℕ) : ∃ y : CircleChartInterval, circleChartCoordinate y = x i := by
      apply mem_range.mp
      rw [range_circleChartCoordinate]
      exact hx i
    choose y hy using hi
    exact ⟨y, funext hy⟩

/-- The dense product chart is comeager in the compact circle product. -/
theorem circleChart_range_residual : range circleChart ∈ residual CircleSequences := by
  have hOne (i : ℕ) : {x : CircleSequences | x i ≠ 0} ∈ residual CircleSequences := by
    apply residual_of_dense_open
    · exact isOpen_compl_singleton.preimage (continuous_apply i)
    · have hd : Dense ({0}ᶜ : Set UnitAddCircle) := by
        rw [← range_circleChartCoordinate]
        exact denseRange_circleChartCoordinate
      exact hd.preimage (isOpenMap_eval i)
  simpa only [range_circleChart, setOf_forall] using countable_iInter_mem.mpr hOne

/-- Dense embeddings preserve residual assertions by preimage. -/
theorem tendsto_residual_of_denseEmbedding {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] {f : A → B}
    (hf : IsEmbedding f) (hd : DenseRange f) : Tendsto f (residual A) (residual B) := by
  apply le_countableGenerate_iff_of_countableInterFilter.mpr
  rintro U ⟨hUo, hUd⟩
  apply residual_of_dense_open (hUo.preimage hf.continuous)
  apply dense_iff_inter_open.mpr
  intro V hVo hVn
  obtain ⟨W, hWo, hWV⟩ := hf.isInducing.isOpen_iff.mp hVo
  obtain ⟨a, haV⟩ := hVn
  have haW : f a ∈ W := by change a ∈ f ⁻¹' W; rw [hWV]; exact haV
  obtain ⟨b, hbW, hbU⟩ := hUd.inter_open_nonempty W hWo ⟨f a, haW⟩
  obtain ⟨z, hzWU, hzRange⟩ := hd.inter_open_nonempty (W ∩ U) (hWo.inter hUo) ⟨b, hbW, hbU⟩
  obtain ⟨a', rfl⟩ := hzRange
  exact ⟨a', by rw [← hWV]; exact hzWU.1, hzWU.2⟩




end BenchmarkJump
end
end Source55
end BenchmarkCountableProof

/- Whole source module: IntervalInterpolation -/
namespace BenchmarkCountableProof
section Source56
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

def affineMix (q : ℝ) (p : ℝ × ℝ) : ℝ := (1 - q) * p.1 + q * p.2

theorem continuous_affineMix (q : ℝ) : Continuous (affineMix q) := by
  unfold affineMix
  fun_prop

theorem isOpenMap_affineMix (q : ℝ) : IsOpenMap (affineMix q) := by
  by_cases hq : q = 1
  · subst q
    have heq : affineMix 1 = (@Prod.snd ℝ ℝ) := by
      funext p
      unfold affineMix
      ring
    rw [heq]
    exact isOpenMap_snd
  have hne : (1 - q : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  intro W hW
  have heq : affineMix q '' W = ⋃ y : ℝ,
      (fun x : ℝ => (1 - q) * x + q * y) '' {x | (x, y) ∈ W} := by
    ext z
    constructor
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      exact mem_iUnion.mpr ⟨y, x, hxy, rfl⟩
    · intro hz
      obtain ⟨y, x, hxy, hxz⟩ := mem_iUnion.mp hz
      exact ⟨(x, y), hxy, hxz⟩
  rw [heq]
  apply isOpen_iUnion
  intro y
  have hmul : IsOpenMap (fun x : ℝ => (1 - q) * x) := isOpenMap_smul₀ hne
  exact ((isOpenMap_add_right (q * y)).comp hmul) _
    (hW.preimage (continuous_id.prodMk continuous_const))

def intervalMix (a b q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (p : Set.Ioo a b × Set.Ioo a b) : Set.Ioo a b :=
  ⟨affineMix q (p.1, p.2), by
    simpa only [affineMix, smul_eq_mul] using
      (convex_Ioo a b) p.1.property p.2.property
        (sub_nonneg.mpr hq1) hq0 (by ring : 1 - q + q = 1)⟩

theorem continuous_intervalMix (a b q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Continuous (intervalMix a b q hq0 hq1) :=
  ((continuous_affineMix q).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _

theorem isOpenMap_intervalMix (a b q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsOpenMap (intervalMix a b q hq0 hq1) := by
  have hInc : IsOpenMap
      (fun p : Set.Ioo a b × Set.Ioo a b => ((p.1 : ℝ), (p.2 : ℝ))) :=
    isOpen_Ioo.isOpenMap_subtype_val.prodMap isOpen_Ioo.isOpenMap_subtype_val
  exact ((isOpenMap_affineMix q).comp hInc).subtype_mk _

theorem intervalMix_surjective (a b q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Function.Surjective (intervalMix a b q hq0 hq1) := by
  intro x
  refine ⟨(x, x), ?_⟩
  apply Subtype.ext
  change (1 - q) * (x : ℝ) + q * (x : ℝ) = (x : ℝ)
  ring

abbrev IntervalBox (a b : ℕ → ℝ) := ∀ i, Set.Ioo (a i) (b i)

def boxPairHomeomorph (a b : ℕ → ℝ) :
    (IntervalBox a b × IntervalBox a b) ≃ₜ
      (∀ i, Set.Ioo (a i) (b i) × Set.Ioo (a i) (b i)) where
  toFun p i := (p.1 i, p.2 i)
  invFun p := (fun i => (p i).1, fun i => (p i).2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_fst).prodMk
      ((continuous_apply i).comp continuous_snd)
  continuous_invFun :=
    (continuous_pi fun i => continuous_fst.comp (continuous_apply i)).prodMk
      (continuous_pi fun i => continuous_snd.comp (continuous_apply i))

def boxMix (a b : ℕ → ℝ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (p : IntervalBox a b × IntervalBox a b) : IntervalBox a b :=
  fun i => intervalMix (a i) (b i) q hq0 hq1 (p.1 i, p.2 i)

theorem continuous_boxMix (a b : ℕ → ℝ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Continuous (boxMix a b q hq0 hq1) :=
  (continuous_pi fun i => (continuous_intervalMix (a i) (b i) q hq0 hq1).comp
    (((continuous_apply i).comp continuous_fst).prodMk
      ((continuous_apply i).comp continuous_snd)))

theorem isOpenMap_boxMix (a b : ℕ → ℝ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsOpenMap (boxMix a b q hq0 hq1) :=
  (IsOpenMap.piMap
    (fun i => isOpenMap_intervalMix (a i) (b i) q hq0 hq1)
    (Eventually.of_forall fun i => intervalMix_surjective (a i) (b i) q hq0 hq1)).comp
      (boxPairHomeomorph a b).isOpenMap

theorem affineMix_difference (x y q r : ℝ) :
    |affineMix q (x, y) - affineMix r (x, y)| = |q - r| * |y - x| := by
  have heq : affineMix q (x, y) - affineMix r (x, y) = (q - r) * (y - x) := by
    unfold affineMix
    ring
  rw [heq, abs_mul]

/-- The uniform coordinate estimate for interpolation in a bounded chart. -/
theorem circle_affineMix_bound (x y q r : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ‖(affineMix q (x, y) : UnitAddCircle) -
      (affineMix r (x, y) : UnitAddCircle)‖ ≤ |q - r| := by
  have hxy : |y - x| ≤ (1 : ℝ) := abs_le.mpr ⟨by linarith [hy.1, hx.2],
    by linarith [hy.2, hx.1]⟩
  calc
    _ = ‖((affineMix q (x, y) - affineMix r (x, y) : ℝ) : UnitAddCircle)‖ := by
      rw [AddCircle.coe_sub]
    _ ≤ |affineMix q (x, y) - affineMix r (x, y)| := by
      simpa only [Real.norm_eq_abs] using
        (QuotientAddGroup.norm_mk_le_norm
          (m := affineMix q (x, y) - affineMix r (x, y))
          (S := AddSubgroup.zmultiples (1 : ℝ)))
    _ = |q - r| * |y - x| := affineMix_difference x y q r
    _ ≤ |q - r| * 1 := mul_le_mul_of_nonneg_left hxy (abs_nonneg _)
    _ = |q - r| := mul_one _




end BenchmarkJump
end
end Source56
end BenchmarkCountableProof

/- Whole source module: LpPrefixInterpolation -/
namespace BenchmarkCountableProof
section Source57
/-! Open finite-prefix affine interpolation in the product of real lines. -/

open Filter Set Topology TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace BenchmarkCountableReverse

open BenchmarkJump

def realPairHomeomorph : (RealSequences × RealSequences) ≃ₜ (ℕ → ℝ × ℝ) where
  toFun q i := (q.1 i, q.2 i)
  invFun q := (fun i => (q i).1, fun i => (q i).2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)
  continuous_invFun := (continuous_pi fun i => continuous_fst.comp (continuous_apply i)).prodMk
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))

def prefixMix (N : ℕ) (q : ℝ) (z : RealSequences × RealSequences) : RealSequences :=
  fun i => affineMix (if i < N then q else 0) (z.1 i, z.2 i)

lemma continuous_prefixMix (N : ℕ) (q : ℝ) : Continuous (prefixMix N q) :=
  continuous_pi fun i => (continuous_affineMix _).comp
    (((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd))

lemma isOpenMap_prefixMix (N : ℕ) (q : ℝ) : IsOpenMap (prefixMix N q) := by
  have hs (i : ℕ) : Function.Surjective (affineMix (if i < N then q else 0)) := by
    intro x
    refine ⟨(x, x), ?_⟩
    unfold affineMix
    ring
  exact (IsOpenMap.piMap (fun i => isOpenMap_affineMix _)
    (Eventually.of_forall hs)).comp realPairHomeomorph.isOpenMap

def PrefixConvex (C : Set RealSequences) : Prop :=
  ∀ N q, 0 ≤ q → q ≤ 1 → ∀ x ∈ C, ∀ y ∈ C, prefixMix N q (x, y) ∈ C

theorem exists_open_prefixConvex_subset (V : Set RealSequences)
    (hVo : IsOpen V) (hVn : V.Nonempty) :
    ∃ C : Set RealSequences, IsOpen C ∧ C.Nonempty ∧ C ⊆ V ∧ PrefixConvex C := by
  classical
  obtain ⟨x, hx⟩ := hVn
  obtain ⟨I, U, hU, hUV⟩ := isOpen_pi_iff.mp hVo x hx
  have hB (i : ℕ) (hi : i ∈ I) :
      ∃ ε > (0 : ℝ), Metric.ball (x i) ε ⊆ U i :=
    Metric.isOpen_iff.mp (hU i hi).1 (x i) (hU i hi).2
  choose ε hεpos hεsub using hB
  let r : ℕ → ℝ := fun i => if hi : i ∈ I then ε i hi else 1
  let C : Set RealSequences := (I : Set ℕ).pi fun i => Metric.ball (x i) (r i)
  have hCr (i : ℕ) (hi : i ∈ I) : 0 < r i := by simpa [r, hi] using hεpos i hi
  refine ⟨C, isOpen_set_pi I.finite_toSet (fun _ _ => Metric.isOpen_ball), ?_, ?_, ?_⟩
  · exact ⟨x, fun i hi => Metric.mem_ball_self (hCr i hi)⟩
  · intro y hy
    apply hUV
    intro i hi
    change i ∈ I at hi
    apply hεsub i hi
    simpa [r, hi] using hy i hi
  · intro N q hq0 hq1 y hy z hz i hi
    by_cases hin : i < N
    · have hyD : |y i - x i| < r i := hy i hi
      have hzD : |z i - x i| < r i := hz i hi
      have hyR : y i ∈ Ioo (x i - r i) (x i + r i) :=
        ⟨by linarith [(abs_lt.mp hyD).1], by linarith [(abs_lt.mp hyD).2]⟩
      have hzR : z i ∈ Ioo (x i - r i) (x i + r i) :=
        ⟨by linarith [(abs_lt.mp hzD).1], by linarith [(abs_lt.mp hzD).2]⟩
      have hm := (convex_Ioo (x i - r i) (x i + r i)) hyR hzR
        (sub_nonneg.mpr hq1) hq0 (by ring : 1 - q + q = 1)
      change x i - r i < affineMix q (y i, z i) ∧ affineMix q (y i, z i) < x i + r i at hm
      change |prefixMix N q (y, z) i - x i| < r i
      simp only [prefixMix, if_pos hin]
      apply abs_lt.mpr
      constructor <;> linarith [hm.1, hm.2]
    · simpa [prefixMix, hin, affineMix] using hy i hi

def prefixMixOn (C : Set RealSequences) (hC : PrefixConvex C)
    (N : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (z : C × C) : C :=
  ⟨prefixMix N q (z.1, z.2), hC N q hq0 hq1 z.1 z.1.property z.2 z.2.property⟩

lemma continuous_prefixMixOn (C : Set RealSequences) (hC : PrefixConvex C)
    (N : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Continuous (prefixMixOn C hC N q hq0 hq1) :=
  ((continuous_prefixMix N q).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _

lemma isOpenMap_prefixMixOn (C : Set RealSequences) (hCo : IsOpen C) (hC : PrefixConvex C)
    (N : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsOpenMap (prefixMixOn C hC N q hq0 hq1) :=
  ((isOpenMap_prefixMix N q).comp
    (hCo.isOpenMap_subtype_val.prodMap hCo.isOpenMap_subtype_val)).subtype_mk _

def prefixVector (p : ℝ≥0∞) (N : ℕ) (x : RealSequences) : Translations p :=
  ∑ i ∈ Finset.range N, lp.single p i (x i)

lemma prefixVector_apply (p : ℝ≥0∞) (N : ℕ) (x : RealSequences) (i : ℕ) :
    prefixVector p N x i = if i < N then x i else 0 := by
  simp only [prefixVector, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single, Finset.mem_range]

lemma prefixMix_add_vector (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (N : ℕ) (q r : ℝ) (x y : RealSequences) :
    prefixMix N q (x, y) = prefixMix N r (x, y) +
      coordinates p ((q - r) • prefixVector p N (y - x)) := by
  funext i
  change affineMix (if i < N then q else 0) (x i, y i) =
    affineMix (if i < N then r else 0) (x i, y i) +
      ((q - r) • prefixVector p N (y - x)) i
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, prefixVector_apply]
  by_cases hi : i < N <;> simp only [hi, ite_true, ite_false, Pi.sub_apply, affineMix] <;> ring

lemma prefixMix_zero (N : ℕ) (x y : RealSequences) : prefixMix N 0 (x, y) = x := by
  funext i
  simp [prefixMix, affineMix]

lemma tendsto_prefixMix_one (x y : RealSequences) :
    Tendsto (fun N : ℕ => prefixMix N 1 (x, y)) atTop (𝓝 y) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop i] with N hN
  simp [prefixMix, hN, affineMix]

end BenchmarkCountableReverse
end
end Source57
end BenchmarkCountableProof

/- Whole source module: LpCountableLocal -/
namespace BenchmarkCountableProof
section Source58
/-! A countable orbit match yields exact equality on small Lp local-orbit pairs. -/

open Filter Set Topology TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace BenchmarkCountableReverse

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

abbrev TranslationTriples := RealSequences × (Translations p × Translations p)

def tripleFirst (t : TranslationTriples p) : RealSequences × Translations p := (t.1, t.2.1)
def tripleSecond (t : TranslationTriples p) : RealSequences × Translations p := (t.1, t.2.2)
def tripleEndpoints (t : TranslationTriples p) : RealSequences × RealSequences :=
  (translationAction p (tripleFirst p t), translationAction p (tripleSecond p t))

lemma continuous_tripleFirst : Continuous (tripleFirst p) :=
  continuous_fst.prodMk (continuous_fst.comp continuous_snd)
lemma continuous_tripleSecond : Continuous (tripleSecond p) :=
  continuous_fst.prodMk (continuous_snd.comp continuous_snd)
lemma isOpenMap_tripleFirst : IsOpenMap (tripleFirst p) := IsOpenMap.id.prodMap isOpenMap_fst
lemma isOpenMap_tripleSecond : IsOpenMap (tripleSecond p) := IsOpenMap.id.prodMap isOpenMap_snd
lemma continuous_tripleEndpoints : Continuous (tripleEndpoints p) :=
  ((continuous_translationAction p).comp (continuous_tripleFirst p)).prodMk
    ((continuous_translationAction p).comp (continuous_tripleSecond p))

theorem good_triples
    (U : Set RealSequences) (W : Set (Translations p)) (D : Set RealSequences)
    (hD : D ∈ residual RealSequences) (f : RealSequences → BenchmarkShift.Point)
    (g : BenchmarkShift.Group)
    (hRes : ∀ᶠ a in residual (RealSequences × Translations p),
      a ∈ U ×ˢ W → f (translationAction p a) = BenchmarkShift.shift g (f a.1)) :
    ∀ᶠ t in residual (TranslationTriples p), t ∈ U ×ˢ (W ×ˢ W) →
      tripleEndpoints p t ∈ D ×ˢ D ∧ f (tripleEndpoints p t).1 = f (tripleEndpoints p t).2 := by
  have h1 := tendsto_residual_of_isOpenMap (continuous_tripleFirst p) (isOpenMap_tripleFirst p) hRes
  have h2 := tendsto_residual_of_isOpenMap (continuous_tripleSecond p) (isOpenMap_tripleSecond p) hRes
  have hD1 := tendsto_residual_of_isOpenMap
    ((continuous_translationAction p).comp (continuous_tripleFirst p))
    ((isOpenMap_translationAction p).comp (isOpenMap_tripleFirst p)) hD
  have hD2 := tendsto_residual_of_isOpenMap
    ((continuous_translationAction p).comp (continuous_tripleSecond p))
    ((isOpenMap_translationAction p).comp (isOpenMap_tripleSecond p)) hD
  filter_upwards [h1, h2, hD1, hD2] with t ht1 ht2 htD1 htD2 hrect
  exact ⟨⟨htD1, htD2⟩, (ht1 ⟨hrect.1, hrect.2.1⟩).trans
    (ht2 ⟨hrect.1, hrect.2.2⟩).symm⟩

lemma open_subset_closure_residual {T : Type*} [TopologicalSpace T] [BaireSpace T]
    (O G : Set T) (hOo : IsOpen O) (hG : G ∈ residual T) : O ⊆ closure (O ∩ G) := by
  intro x hx
  apply mem_closure_iff.mpr
  intro V hVo hxV
  obtain ⟨y, ⟨hyV, hyO⟩, hyG⟩ :=
    (dense_of_mem_residual hG).inter_open_nonempty (V ∩ O) (hVo.inter hOo) ⟨x, hxV, hx⟩
  exact ⟨y, hyV, hyO, hyG⟩

lemma equality_of_mem_closure
    (D : Set RealSequences) (f : RealSequences → BenchmarkShift.Point) (hf : ContinuousOn f D)
    (S : Set (RealSequences × RealSequences)) (hSD : S ⊆ D ×ˢ D)
    (hEq : ∀ q ∈ S, f q.1 = f q.2) (q : RealSequences × RealSequences)
    (hqD : q ∈ D ×ˢ D) (hq : q ∈ closure S) : f q.1 = f q.2 := by
  have hc := ((hf q.1 hqD.1).prodMap (hf q.2 hqD.2)).mono hSD
  have hm : MapsTo (Prod.map f f) S
      {r : BenchmarkShift.Point × BenchmarkShift.Point | r.1 = r.2} := hEq
  have hcl := hc.mem_closure hq hm
  simpa only [(isClosed_eq continuous_fst continuous_snd).closure_eq] using hcl

theorem small_translation_exact
    (U : Set RealSequences) (W : Set (Translations p)) (hUo : IsOpen U) (hWo : IsOpen W)
    (D : Set RealSequences) (hD : D ∈ residual RealSequences)
    (f : RealSequences → BenchmarkShift.Point) (hf : ContinuousOn f D)
    (g : BenchmarkShift.Group)
    (hRes : ∀ᶠ a in residual (RealSequences × Translations p),
      a ∈ U ×ˢ W → f (translationAction p a) = BenchmarkShift.shift g (f a.1))
    (h₀ : Translations p) (hh₀ : h₀ ∈ W) (ε : ℝ) (hBall : Metric.ball h₀ ε ⊆ W)
    (x : RealSequences) (hx : x ∈ U) (k : Translations p) (hk : ‖k‖ < ε)
    (hyD : translationAction p (x, h₀) ∈ D)
    (hzD : translationAction p (x, h₀ + k) ∈ D) :
    f (translationAction p (x, h₀)) = f (translationAction p (x, h₀ + k)) := by
  let Ω : Set (TranslationTriples p) := U ×ˢ (W ×ˢ W)
  let G : Set (TranslationTriples p) := {t | t ∈ Ω →
    tripleEndpoints p t ∈ D ×ˢ D ∧ f (tripleEndpoints p t).1 = f (tripleEndpoints p t).2}
  have hG : G ∈ residual (TranslationTriples p) := good_triples p U W D hD f g hRes
  let S := Ω ∩ G
  have hclosure : Ω ⊆ closure S :=
    open_subset_closure_residual Ω G (hUo.prod (hWo.prod hWo)) hG
  let t : TranslationTriples p := (x, h₀, h₀ + k)
  have ht : t ∈ Ω := by
    refine ⟨hx, hh₀, hBall ?_⟩
    change dist (h₀ + k) h₀ < ε
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hk
  have himg : tripleEndpoints p t ∈ closure (tripleEndpoints p '' S) :=
    image_closure_subset_closure_image (continuous_tripleEndpoints p) ⟨t, hclosure ht, rfl⟩
  apply equality_of_mem_closure D f hf (tripleEndpoints p '' S)
    (fun q hq => ?_) (fun q hq => ?_) (tripleEndpoints p t) ⟨hyD, hzD⟩ himg
  · obtain ⟨s, hs, rfl⟩ := hq
    exact (hs.2 hs.1).1
  · obtain ⟨s, hs, rfl⟩ := hq
    exact (hs.2 hs.1).2

end BenchmarkCountableReverse
end
end Source58
end BenchmarkCountableProof

/- Whole source module: LpGenericConstancy -/
namespace BenchmarkCountableProof
section Source59
/-! Finite-prefix interpolation propagates exact local-orbit equality to
generic constancy on a product-open set. -/

open Filter Set Topology TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace BenchmarkCountableReverse

def fraction (m : ℕ) (j : Fin (m + 1)) : ℝ := (j : ℝ) / m

lemma fraction_nonneg (m : ℕ) (j : Fin (m + 1)) : 0 ≤ fraction m j := by
  unfold fraction
  positivity

lemma fraction_le_one (m : ℕ) (j : Fin (m + 1)) : fraction m j ≤ 1 := by
  by_cases hm : m = 0
  · subst m
    simp [fraction]
  · unfold fraction
    apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hm)).mpr
    exact_mod_cast Nat.le_of_lt_succ j.isLt

lemma fraction_step (m : ℕ) (hm : 0 < m) (j : Fin m) :
    fraction m j.succ - fraction m j.castSucc = 1 / (m : ℝ) := by
  unfold fraction
  simp only [Fin.coe_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  ring

lemma fraction_last (m : ℕ) (hm : 0 < m) : fraction m (Fin.last m) = 1 := by
  simp [fraction, (by exact_mod_cast hm.ne' : (m : ℝ) ≠ 0)]

theorem prefix_interpolation_generic_pairs (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (C : Set RealSequences) (hCo : IsOpen C) (hC : PrefixConvex C)
    (D : Set RealSequences) (hD : D ∈ residual RealSequences)
    (f : RealSequences → BenchmarkShift.Point) (hf : ContinuousOn f D)
    (ε : ℝ) (hε : 0 < ε)
    (hSmall : ∀ y ∈ C, ∀ k : Translations p, ‖k‖ < ε →
      y ∈ D → y + coordinates p k ∈ D → f y = f (y + coordinates p k)) :
    ∀ᶠ z : C × C in residual (C × C), f z.1 = f z.2 := by
  classical
  let P (N m : ℕ) (j : Fin (m + 1)) : C × C → C :=
    prefixMixOn C hC N (fraction m j) (fraction_nonneg m j) (fraction_le_one m j)
  have hDC : ∀ᶠ x : C in residual C, (x : RealSequences) ∈ D :=
    BenchmarkJump.eventually_residual_open_subspace C hCo hD
  have hAll : ∀ᶠ z : C × C in residual (C × C),
      ∀ N m : ℕ, ∀ j : Fin (m + 1), (P N m j z : RealSequences) ∈ D := by
    apply eventually_countable_forall.mpr
    intro N
    apply eventually_countable_forall.mpr
    intro m
    apply eventually_countable_forall.mpr
    intro j
    exact tendsto_residual_of_isOpenMap (continuous_prefixMixOn C hC N _ _ _)
      (isOpenMap_prefixMixOn C hCo hC N _ _ _) hDC
  have hD1 : ∀ᶠ z : C × C in residual (C × C), (z.1 : RealSequences) ∈ D :=
    tendsto_residual_of_isOpenMap continuous_fst isOpenMap_fst hDC
  have hD2 : ∀ᶠ z : C × C in residual (C × C), (z.2 : RealSequences) ∈ D :=
    tendsto_residual_of_isOpenMap continuous_snd isOpenMap_snd hDC
  filter_upwards [hAll, hD1, hD2] with z hz hz1 hz2
  have hChain (N : ℕ) : f z.1 = f (prefixMix N 1 (z.1, z.2)) := by
    let v := prefixVector p N ((z.2 : RealSequences) - (z.1 : RealSequences))
    obtain ⟨m, hm⟩ := exists_nat_gt (‖v‖ / ε)
    have hmpos : 0 < m := by
      have hmreal : (0 : ℝ) < m := lt_of_le_of_lt (div_nonneg (norm_nonneg _) hε.le) hm
      exact_mod_cast hmreal
    have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
    have hvdiv : ‖v‖ / (m : ℝ) < ε := by
      apply (div_lt_iff₀ hmreal).mpr
      have hv := (div_lt_iff₀ hε).mp hm
      linarith
    have hStep (j : Fin m) : f (P N m j.castSucc z) = f (P N m j.succ z) := by
      let k : Translations p :=
        (fraction m j.succ - fraction m j.castSucc) • v
      have hk : ‖k‖ < ε := by
        dsimp only [k]
        rw [norm_smul, Real.norm_eq_abs, fraction_step m hmpos j,
          abs_of_pos (div_pos zero_lt_one hmreal)]
        simpa only [one_div, mul_comm, div_eq_mul_inv, mul_one] using hvdiv
      have heq : (P N m j.succ z : RealSequences) =
          (P N m j.castSucc z : RealSequences) + coordinates p k :=
        prefixMix_add_vector p N _ _ z.1 z.2
      have h := hSmall (P N m j.castSucc z) (P N m j.castSucc z).property
        k hk (hz N m j.castSucc) (by rw [← heq]; exact hz N m j.succ)
      rwa [← heq] at h
    have hAux : ∀ j : ℕ, ∀ hj : j ≤ m,
        f (P N m 0 z) = f (P N m ⟨j, Nat.lt_succ_of_le hj⟩ z) := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
          intro hj
          have hjm : j < m := by omega
          exact (ih (by omega)).trans (hStep ⟨j, hjm⟩)
    have he := hAux m le_rfl
    have hstart : (P N m 0 z : RealSequences) = z.1 := by
      change prefixMix N (fraction m 0) (z.1, z.2) = _
      simp only [fraction, Fin.val_zero, Nat.cast_zero, zero_div]
      exact prefixMix_zero N z.1 z.2
    have hend : (P N m (Fin.last m) z : RealSequences) = prefixMix N 1 (z.1, z.2) := by
      change prefixMix N (fraction m (Fin.last m)) (z.1, z.2) = _
      rw [fraction_last m hmpos]
    change f (P N m 0 z) = f (P N m (Fin.last m) z) at he
    rwa [hstart, hend] at he
  have hMixD (N : ℕ) : prefixMix N 1 ((z.1 : RealSequences), z.2) ∈ D := by
    simpa only [P, prefixMixOn, fraction_last 1 (by norm_num)] using hz N 1 (Fin.last 1)
  let S : Set (RealSequences × RealSequences) := {q | q ∈ D ×ˢ D ∧ f q.1 = f q.2}
  apply equality_of_mem_closure D f hf S (fun q hq => hq.1) (fun q hq => hq.2)
    ((z.1 : RealSequences), z.2) ⟨hz1, hz2⟩
  apply mem_closure_of_tendsto
    (tendsto_const_nhds.prodMk_nhds (tendsto_prefixMix_one z.1 z.2))
  exact Eventually.of_forall fun N => ⟨⟨hz1, hMixD N⟩, hChain N⟩

theorem prefix_interpolation_generic_constant (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (C : Set RealSequences) (hCo : IsOpen C) (hCn : C.Nonempty) (hC : PrefixConvex C)
    (D : Set RealSequences) (hD : D ∈ residual RealSequences)
    (f : RealSequences → BenchmarkShift.Point) (hf : ContinuousOn f D)
    (ε : ℝ) (hε : 0 < ε)
    (hSmall : ∀ y ∈ C, ∀ k : Translations p, ‖k‖ < ε →
      y ∈ D → y + coordinates p k ∈ D → f y = f (y + coordinates p k)) :
    ∃ a : BenchmarkShift.Point, ∀ᶠ x : C in residual C, f x = a := by
  letI : Nonempty C := hCn.to_subtype
  letI : BaireSpace C := hCo.baireSpace
  obtain ⟨x, hx⟩ := BenchmarkJump.exists_residual_section
    (prefix_interpolation_generic_pairs p C hCo hC D hD f hf ε hε hSmall)
  exact ⟨f x, hx.mono fun y hy => hy.symm⟩

end BenchmarkCountableReverse
end
end Source59
end BenchmarkCountableProof

/- Whole source module: LpClassMeagre -/
namespace BenchmarkCountableProof
section Source60
/-! Every finite-Lp class is meager in the actual product of real lines. -/

open Filter Set Topology TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace BenchmarkCountableReverse

def coordinateBound (a : RealSequences) (M : ℕ) : Set RealSequences :=
  {x | ∀ i, |x i - a i| ≤ M}

lemma isClosed_coordinateBound (a : RealSequences) (M : ℕ) :
    IsClosed (coordinateBound a M) := by
  unfold coordinateBound
  simp only [setOf_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_le (((continuous_apply i).sub continuous_const).abs) continuous_const

lemma interior_coordinateBound (a : RealSequences) (M : ℕ) :
    interior (coordinateBound a M) = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.2
  intro x hx
  obtain ⟨I, V, hV, hVI⟩ := isOpen_pi_iff.mp isOpen_interior x hx
  let k := I.sup id + 1
  have hkI : k ∉ I := by
    intro hk
    have h := Finset.le_sup (f := id) hk
    change I.sup id + 1 ≤ I.sup id at h
    omega
  let y := Function.update x k (a k + ((M : ℝ) + 1))
  have hy : y ∈ (I : Set ℕ).pi V := by
    intro i hi
    have hin : i ≠ k := by intro h; exact hkI (h ▸ hi)
    simpa only [y, Function.update_of_ne hin] using (hV i hi).2
  have hbad := interior_subset (hVI hy) k
  have heq : |y k - a k| = (M : ℝ) + 1 := by
    simp [y, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (M : ℝ) + 1)]
  rw [heq] at hbad
  linarith

theorem lp_class_meagre (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (a : RealSequences) :
    IsMeagre {x | BenchmarkComparisons.LpDifference p.toReal a x} := by
  have hM (M : ℕ) : IsMeagre (coordinateBound a M) :=
    ((isClosed_coordinateBound a M).isNowhereDense_iff.mpr (interior_coordinateBound a M)).isMeagre
  apply (isMeagre_iUnion hM).mono
  intro x hx
  have hpos : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
  have hmem : Memℓp (fun i => a i - x i) p :=
    (memℓp_gen_iff hpos).mpr (by simpa only [Real.norm_eq_abs] using hx)
  let v : Translations p := ⟨fun i => a i - x i, hmem⟩
  obtain ⟨M, hM⟩ := exists_nat_gt ‖v‖
  apply mem_iUnion.mpr
  refine ⟨M, fun i => ?_⟩
  have hb := lp.norm_apply_le_norm (p := p) (zero_lt_one.trans_le Fact.out).ne' v i
  have heq : ‖v i‖ = |x i - a i| := by simp only [v, Real.norm_eq_abs, abs_sub_comm]
  rw [heq] at hb
  exact hb.trans hM.le

end BenchmarkCountableReverse
end
end Source60
end BenchmarkCountableProof

/- Whole source module: LpCountableObstruction -/
namespace BenchmarkCountableProof
section Source61
/-! Unconditional nonreducibility of every finite real-sequence Lp relation
to the actual full binary free-group orbit relation. -/

open Filter Set Topology TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace BenchmarkCountableReverse

theorem finite_ENNlp_not_reduces_eInfinity (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ¬ BenchmarkComparisons.BorelReduces (BenchmarkComparisons.LpDifference p.toReal)
      BenchmarkComparisons.EInfinity := by
  rintro ⟨f, hf, hred⟩
  obtain ⟨g, U, W, hUo, hUn, hWo, hWn, hRes⟩ := countable_orbit_rectangle p hp f hf
    (fun x y hxy => (hred x y).mp hxy)
  obtain ⟨h₀, hh₀⟩ := hWn
  obtain ⟨ε, hε, hBall⟩ := Metric.isOpen_iff.mp hWo h₀ hh₀
  obtain ⟨D, hDG, hDd, hfD⟩ := BenchmarkJump.measurable_continuousOn_residual f hf
  have hD : D ∈ residual RealSequences := residual_of_dense_Gδ hDG hDd
  let A : Set RealSequences := (fun x => x + coordinates p h₀) '' U
  have hAo : IsOpen A := isOpenMap_add_right (coordinates p h₀) _ hUo
  have hAn : A.Nonempty := hUn.image _
  obtain ⟨C, hCo, hCn, hCA, hC⟩ := exists_open_prefixConvex_subset A hAo hAn
  have hSmall : ∀ y ∈ C, ∀ k : Translations p, ‖k‖ < ε →
      y ∈ D → y + coordinates p k ∈ D → f y = f (y + coordinates p k) := by
    intro y hyC k hk hyD hzD
    obtain ⟨x, hxU, hxy⟩ := hCA hyC
    have hbase : translationAction p (x, h₀) = y := hxy
    have hnext : translationAction p (x, h₀ + k) = y + coordinates p k := by
      change x + coordinates p (h₀ + k) = y + coordinates p k
      rw [← hxy]
      change x + (coordinates p h₀ + coordinates p k) = (x + coordinates p h₀) + coordinates p k
      abel
    have he := small_translation_exact p U W hUo hWo D hD f hfD g hRes
      h₀ hh₀ ε hBall x hxU k hk (hbase.symm ▸ hyD) (hnext.symm ▸ hzD)
    simpa only [hbase, hnext] using he
  obtain ⟨a, ha⟩ := prefix_interpolation_generic_constant p C hCo hCn hC D hD f hfD ε hε hSmall
  letI : Nonempty C := hCn.to_subtype
  letI : BaireSpace C := hCo.baireSpace
  obtain ⟨x₀, hx₀⟩ := (dense_of_mem_residual ha).nonempty
  have hnot : ∀ᶠ y : C in residual C,
      ¬ BenchmarkComparisons.LpDifference p.toReal (x₀ : RealSequences) y :=
    tendsto_residual_of_isOpenMap continuous_subtype_val hCo.isOpenMap_subtype_val
      (lp_class_meagre p hp x₀)
  have hfalse : ∀ᶠ y : C in residual C, False := by
    filter_upwards [ha, hnot] with y hy hny
    apply hny
    apply (hred x₀ y).mpr
    rw [hx₀, hy]
    exact ⟨1, by intro h; simp⟩
  obtain ⟨y, hy⟩ := (dense_of_mem_residual hfalse).nonempty
  exact hy

theorem finiteLp_not_reduces_eInfinity (p : ℝ) (hp : 1 ≤ p) :
    ¬ BenchmarkComparisons.BorelReduces (BenchmarkComparisons.LpDifference p)
      BenchmarkComparisons.EInfinity := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  have h := finite_ENNlp_not_reduces_eInfinity (ENNReal.ofReal p) ENNReal.ofReal_ne_top
  simpa only [ENNReal.toReal_ofReal (le_trans zero_le_one hp)] using h

end BenchmarkCountableReverse
end
end Source61
end BenchmarkCountableProof

/- Whole source module: CountableComparisonsMission -/
namespace BenchmarkCountableProof
section Source62
/-! The exact complete benchmark mission statement for Theorem 1.1. -/

namespace BenchmarkCountableComparisons

theorem countable_comparisons : BenchmarkComparisons.CountableComparisons := by
  refine ⟨BenchmarkCountablePositive.product_eInfinity_reduces_null, ?_⟩
  intro p hp
  exact ⟨BenchmarkShift.eInfinity_not_reduces_finiteLp p hp,
    BenchmarkCountableReverse.finiteLp_not_reduces_eInfinity p hp⟩

end BenchmarkCountableComparisons
end Source62
end BenchmarkCountableProof

theorem solution : BenchmarkComparisons.CountableComparisons := by
  exact BenchmarkCountableProof.BenchmarkCountableComparisons.countable_comparisons

#print axioms solution
