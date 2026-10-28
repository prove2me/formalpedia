-- Prove2me | solution 1 for BenchmarkComparisons.countable_product_to_c0
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T07:43:58.731038+00:00
-- url     : https://prove2.me/submissions/3f6570eb-3309-4afc-ac68-13c35010b8c7

import Definitions.Def_BenchmarkRelations
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Tactic


/- Whole source module: CountableBorelColoring -/
namespace BenchmarkPositiveProof
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
end BenchmarkPositiveProof

/- Whole source module: FiniteBorelColoring -/
namespace BenchmarkPositiveProof
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
end BenchmarkPositiveProof

/- Whole source module: GraphDistanceBlocks -/
namespace BenchmarkPositiveProof
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
end BenchmarkPositiveProof

/- Whole source module: RefiningFinitePartitions -/
namespace BenchmarkPositiveProof
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
end BenchmarkPositiveProof

/- Whole source module: BoundedGraphNull -/
namespace BenchmarkPositiveProof
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
end BenchmarkPositiveProof

/- Whole source module: ShiftGraph -/
namespace BenchmarkPositiveProof
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
end BenchmarkPositiveProof

/- Whole source module: ShiftFiniteBalls -/
namespace BenchmarkPositiveProof
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
end BenchmarkPositiveProof

/- Whole source module: BoundedNullProduct -/
namespace BenchmarkPositiveProof
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
end BenchmarkPositiveProof

/- Whole source module: ShiftNullReduction -/
namespace BenchmarkPositiveProof
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
end BenchmarkPositiveProof

/- Whole source module: CountablePositiveMission -/
namespace BenchmarkPositiveProof
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
end BenchmarkPositiveProof

theorem solution : BenchmarkComparisons.BorelReduces (BenchmarkComparisons.ProductRelation BenchmarkComparisons.EInfinity) BenchmarkComparisons.NullDifference := by
  exact BenchmarkPositiveProof.BenchmarkCountablePositive.product_eInfinity_reduces_null

#print axioms solution
