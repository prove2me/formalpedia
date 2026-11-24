-- Prove2me | solution 1 for BerggrenHarmonic.bernoulli_isHarmonic
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T07:15:48.451474+00:00
-- url     : https://prove2.me/submissions/7e75654b-a71a-43fd-8e6a-4d04ee064d99

-- Thm stub generated from Bridges/BerggrenHarmonicMeasure.lean
import Mathlib
import Definitions.Def_Bridges_BerggrenHarmonicMeasure

/-!
# Harmonic measure on the boundary of the Berggren tree

The Berggren tree of primitive Pythagorean triples is the free rooted ternary tree on the
three Berggren moves `L, M, R` (the catalog's `HyperbolicBerggrenGeodesics.Move`, whose
words `run : List Move → ℕ × ℕ` enumerate every primitive triple exactly once).  Its
*boundary* — the set of infinite descending paths — is therefore the space of infinite words
over a three letter alphabet,

`Bdry = ℕ → Fin 3`,

the **3-adic Cantor set**.  This file develops the probabilistic theory of the tree:

* `cyl n v` : the cylinder set of boundary points agreeing with `v` on the first `n` letters
  (the shadow of a depth-`n` node of the tree).
* `ProbVec` : a strictly positive probability vector `(p₁, p₂, p₃)` on the three moves.
* `bernoulli P` : the Bernoulli (product) measure on the boundary, built with Mathlib's
  infinite product measure `MeasureTheory.Measure.infinitePi`.
* `IsHarmonic P ν` : the *harmonicity* (stationarity, self-similarity) equation
  `ν = ∑ a, pₐ · (consₐ)_* ν` characterising the hitting distribution on the boundary of the
  random walk which, at each step, appends the letter `a` with probability `pₐ`.

## Main results

* `bernoulli_cyl` : the product measure of a depth-`n` cylinder is `∏_{i<n} p_{v i}`.
* `ext_of_cyl_eq` : two probability measures on the boundary agreeing on all cylinders are
  equal (the cylinders form a π-system generating the product σ-algebra:
  `isPiSystem_cylinders`, `generateFrom_cylinders`).
* `IsHarmonic.cyl_eq` : *every* harmonic measure gives a cylinder its Bernoulli mass.
* `bernoulli_isHarmonic` : the Bernoulli measure is harmonic.
* `harmonic_iff_bernoulli`, `existsUnique_harmonic` : **the harmonic measure of the Berggren
  random walk exists, is unique, and is exactly the Bernoulli product measure** — the main
  conjecture of this cycle, in the strong "unique stationary measure" form.
* `bernoulli_uniform_cyl` : for the uniform walk the harmonic measure of a depth-`n`
  cylinder is `3^{-n}`, i.e. it is the Hausdorff/Cantor measure of the 3-adic boundary.
-/

open BerggrenHarmonic

open MeasureTheory Set MeasurableSpace
open scoped ENNReal













/-! ## Probability vectors and the Bernoulli measure -/


open ProbVec

variable (P : ProbVec)














/-! ## Cylinders generate: a uniqueness tool -/









/-! ## Harmonicity -/

open MeasureTheory Set MeasurableSpace
open scoped ENNReal
namespace BerggrenHarmonic

@[simp] lemma cons_zero (a : Letter) (x : Bdry) : cons a x 0 = a := rfl

end BerggrenHarmonic

namespace BerggrenHarmonic

@[simp] lemma cons_succ (a : Letter) (x : Bdry) (k : ℕ) : cons a x (k + 1) = x k := rfl

end BerggrenHarmonic

namespace BerggrenHarmonic

lemma measurable_cons (a : Letter) : Measurable (cons a) := by
  apply measurable_pi_lambda
  intro n
  cases n with
  | zero => exact measurable_const
  | succ k => exact measurable_pi_apply k

end BerggrenHarmonic

namespace BerggrenHarmonic

@[simp] lemma cyl_zero (v : Bdry) : cyl 0 v = univ := by
  ext x; simp [cyl]

end BerggrenHarmonic

namespace BerggrenHarmonic

lemma cyl_eq_pi (n : ℕ) (v : Bdry) :
    cyl n v = (↑(Finset.range n) : Set ℕ).pi (fun i => {v i}) := by
  ext x
  simp [cyl, Set.mem_pi]

end BerggrenHarmonic

namespace BerggrenHarmonic

lemma measurableSet_cyl (n : ℕ) (v : Bdry) : MeasurableSet (cyl n v) := by
  rw [BerggrenHarmonic.cyl_eq_pi]
  exact MeasurableSet.pi (Finset.range n).countable_toSet (fun i _ => MeasurableSet.singleton _)

end BerggrenHarmonic

namespace BerggrenHarmonic

lemma preimage_cons_cyl_succ (a : Letter) (n : ℕ) (v : Bdry) :
    cons a ⁻¹' cyl (n + 1) v = if a = v 0 then cyl n (tail v) else ∅ := by
  by_cases h : a = v 0
  · simp only [h]
    ext x
    constructor
    · intro hx i hi
      have := hx (i + 1) (by omega)
      simpa [tail] using this
    · intro hx i hi
      cases i with
      | zero => simp
      | succ k =>
          have : x k = tail v k := hx k (by omega)
          simpa [tail] using this
  · simp only [h]
    ext x
    constructor
    · intro hx
      exact absurd (by simpa [cons] using hx 0 (by omega)) h
    · intro hx
      exact hx.elim

end BerggrenHarmonic

namespace BerggrenHarmonic

namespace ProbVec

section
variable (P : ProbVec)

lemma le_one (a : Letter) : P.p a ≤ 1 := by
  have h := P.sum_eq
  have : ∀ b ∈ Finset.univ, 0 ≤ P.p b := fun b _ => (P.pos b).le
  calc P.p a ≤ ∑ b, P.p b := Finset.single_le_sum this (Finset.mem_univ a)
    _ = 1 := h

end

end ProbVec

end BerggrenHarmonic

namespace BerggrenHarmonic

namespace ProbVec

section
variable (P : ProbVec)

@[simp] lemma pmf_apply (a : Letter) : P.pmf a = ENNReal.ofReal (P.p a) := by
  simp [pmf]

end

end ProbVec

end BerggrenHarmonic

namespace BerggrenHarmonic

namespace ProbVec

section
variable (P : ProbVec)

@[simp] lemma stepMeasure_singleton (a : Letter) :
    P.stepMeasure {a} = ENNReal.ofReal (P.p a) := by
  rw [stepMeasure, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton a), BerggrenHarmonic.ProbVec.pmf_apply]

end

end ProbVec

end BerggrenHarmonic

namespace BerggrenHarmonic

@[simp] lemma wmass_zero (P : ProbVec) (v : Bdry) : wmass P 0 v = 1 := by
  simp [wmass]

end BerggrenHarmonic

namespace BerggrenHarmonic

lemma wmass_succ (P : ProbVec) (n : ℕ) (v : Bdry) :
    wmass P (n + 1) v = ENNReal.ofReal (P.p (v 0)) * wmass P n (tail v) := by
  unfold wmass
  rw [Finset.prod_range_succ']
  simp [tail, mul_comm]

end BerggrenHarmonic

namespace BerggrenHarmonic

theorem bernoulli_cyl (P : ProbVec) (n : ℕ) (v : Bdry) :
    bernoulli P (cyl n v) = wmass P n v := by
  rw [BerggrenHarmonic.cyl_eq_pi, bernoulli,
    Measure.infinitePi_pi _ (fun i _ => MeasurableSet.singleton (v i))]
  simp [wmass]

end BerggrenHarmonic

namespace BerggrenHarmonic

lemma cyl_mem_cylinders (n : ℕ) (v : Bdry) : cyl n v ∈ cylinders := ⟨n, v, rfl⟩

end BerggrenHarmonic

namespace BerggrenHarmonic

lemma cyl_subset_of_mem {n m : ℕ} {v w : Bdry} (hnm : n ≤ m) {x : Bdry}
    (hxv : x ∈ cyl n v) (hxw : x ∈ cyl m w) : cyl m w ⊆ cyl n v := by
  intro y hy i hi
  have h1 : y i = w i := hy i (lt_of_lt_of_le hi hnm)
  have h2 : x i = w i := hxw i (lt_of_lt_of_le hi hnm)
  have h3 : x i = v i := hxv i hi
  rw [h1, ← h2, h3]

end BerggrenHarmonic

namespace BerggrenHarmonic

lemma isPiSystem_cylinders : IsPiSystem cylinders := by
  rintro S ⟨n, v, rfl⟩ T ⟨m, w, rfl⟩ ⟨x, hxv, hxw⟩
  rcases le_total n m with h | h
  · have hsub := BerggrenHarmonic.cyl_subset_of_mem h hxv hxw
    have : cyl n v ∩ cyl m w = cyl m w := by
      apply Set.inter_eq_self_of_subset_right hsub
    rw [this]
    exact BerggrenHarmonic.cyl_mem_cylinders m w
  · have hsub := BerggrenHarmonic.cyl_subset_of_mem h hxw hxv
    have : cyl n v ∩ cyl m w = cyl n v := by
      apply Set.inter_eq_self_of_subset_left hsub
    rw [this]
    exact BerggrenHarmonic.cyl_mem_cylinders n v

end BerggrenHarmonic

namespace BerggrenHarmonic

lemma coord_eq_eq_iUnion (i : ℕ) (a : Letter) :
    {x : Bdry | x i = a} =
      ⋃ u : {u : Fin (i + 1) → Letter // u ⟨i, Nat.lt_succ_self i⟩ = a},
        cyl (i + 1) (extend (i + 1) u.1) := by
  ext x
  constructor
  · intro hx
    refine mem_iUnion.2 ⟨⟨fun j => x j, by simpa using hx⟩, ?_⟩
    intro k hk
    simp [extend, hk]
  · intro hx
    obtain ⟨u, hu⟩ := mem_iUnion.1 hx
    have h2 := hu i (Nat.lt_succ_self i)
    simp only [mem_setOf_eq]
    rw [h2]
    simpa [extend] using u.2

end BerggrenHarmonic

namespace BerggrenHarmonic

lemma generateFrom_cylinders :
    MeasurableSpace.generateFrom cylinders = (inferInstance : MeasurableSpace Bdry) := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro S ⟨n, v, rfl⟩
    exact BerggrenHarmonic.measurableSet_cyl n v
  · rw [MeasurableSpace.le_def]
    have hcoord : ∀ i : ℕ, Measurable[MeasurableSpace.generateFrom cylinders]
        (fun x : Bdry => x i) := by
      intro i
      refine @measurable_to_countable' Letter Bdry _ _ (MeasurableSpace.generateFrom cylinders)
        _ (fun a => ?_)
      have hpre : (fun x : Bdry => x i) ⁻¹' {a} = {x : Bdry | x i = a} := rfl
      rw [hpre, BerggrenHarmonic.coord_eq_eq_iUnion i a]
      refine @MeasurableSet.iUnion _ _ (MeasurableSpace.generateFrom cylinders) _ _ (fun u => ?_)
      exact MeasurableSpace.measurableSet_generateFrom (BerggrenHarmonic.cyl_mem_cylinders _ _)
    intro s hs
    have hm : Measurable[MeasurableSpace.generateFrom cylinders] (id : Bdry → Bdry) :=
      (@measurable_pi_iff Bdry ℕ (fun _ => Letter) (MeasurableSpace.generateFrom cylinders)
        _ id).2 hcoord
    exact hm hs

end BerggrenHarmonic

namespace BerggrenHarmonic

theorem ext_of_cyl_eq {μ ν : Measure Bdry} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ n v, μ (cyl n v) = ν (cyl n v)) : μ = ν := by
  refine MeasureTheory.ext_of_generate_finite cylinders BerggrenHarmonic.generateFrom_cylinders.symm
    isPiSystem_cylinders ?_ ?_
  · rintro S ⟨n, v, rfl⟩
    exact h n v
  · rw [measure_univ, measure_univ]

end BerggrenHarmonic

namespace BerggrenHarmonic

lemma isHarmonic_apply {P : ProbVec} {ν : Measure Bdry} (h : IsHarmonic P ν)
    {S : Set Bdry} (hS : MeasurableSet S) :
    ν S = ∑ a : Letter, ENNReal.ofReal (P.p a) * ν (cons a ⁻¹' S) := by
  conv_lhs => rw [h]
  rw [Measure.coe_finset_sum]
  simp only [Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Measure.map_apply (BerggrenHarmonic.measurable_cons a) hS]

end BerggrenHarmonic

namespace BerggrenHarmonic

theorem IsHarmonic.cyl_eq {P : ProbVec} {ν : Measure Bdry} [IsProbabilityMeasure ν]
    (h : IsHarmonic P ν) (n : ℕ) (v : Bdry) : ν (cyl n v) = wmass P n v := by
  induction n generalizing v with
  | zero => rw [BerggrenHarmonic.cyl_zero, BerggrenHarmonic.wmass_zero, measure_univ]
  | succ n ih =>
      rw [BerggrenHarmonic.isHarmonic_apply h (BerggrenHarmonic.measurableSet_cyl (n + 1) v)]
      have hterm : ∀ a : Letter, ENNReal.ofReal (P.p a) * ν (cons a ⁻¹' cyl (n + 1) v)
          = if a = v 0 then ENNReal.ofReal (P.p (v 0)) * wmass P n (tail v) else 0 := by
        intro a
        rw [BerggrenHarmonic.preimage_cons_cyl_succ]
        by_cases ha : a = v 0
        · subst ha
          rw [if_pos rfl, if_pos rfl, ih (tail v)]
        · simp [ha]
      rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_ite_eq' Finset.univ (v 0)]
      simp [BerggrenHarmonic.wmass_succ]

end BerggrenHarmonic

namespace BerggrenHarmonic

theorem bernoulli_isHarmonic (P : ProbVec) : IsHarmonic P (bernoulli P) := by
  set ν : Measure Bdry := ∑ a : Letter, ENNReal.ofReal (P.p a) • (bernoulli P).map (cons a)
    with hν
  have hval : ∀ (S : Set Bdry), MeasurableSet S →
      ν S = ∑ a : Letter, ENNReal.ofReal (P.p a) * bernoulli P (cons a ⁻¹' S) := by
    intro S hS
    rw [hν, Measure.coe_finset_sum]
    simp only [Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Measure.map_apply (BerggrenHarmonic.measurable_cons a) hS]
  have huniv : ν univ = 1 := by
    rw [hval univ MeasurableSet.univ]
    simp only [Set.preimage_univ, measure_univ, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (P.pos a).le), P.sum_eq, ENNReal.ofReal_one]
  have hprob : IsProbabilityMeasure ν := ⟨huniv⟩
  have hcyl : ∀ n v, bernoulli P (cyl n v) = ν (cyl n v) := by
    intro n v
    rw [BerggrenHarmonic.bernoulli_cyl]
    cases n with
    | zero => rw [BerggrenHarmonic.cyl_zero, BerggrenHarmonic.wmass_zero, huniv]
    | succ n =>
        rw [hval _ (BerggrenHarmonic.measurableSet_cyl (n + 1) v)]
        have hterm : ∀ a : Letter, ENNReal.ofReal (P.p a) * bernoulli P (cons a ⁻¹' cyl (n+1) v)
            = if a = v 0 then ENNReal.ofReal (P.p (v 0)) * wmass P n (tail v) else 0 := by
          intro a
          rw [BerggrenHarmonic.preimage_cons_cyl_succ]
          by_cases ha : a = v 0
          · subst ha
            rw [if_pos rfl, if_pos rfl, BerggrenHarmonic.bernoulli_cyl]
          · simp [ha]
        rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_ite_eq' Finset.univ (v 0)]
        simp [BerggrenHarmonic.wmass_succ]
  exact @BerggrenHarmonic.ext_of_cyl_eq _ _ inferInstance hprob hcyl

end BerggrenHarmonic

namespace BerggrenHarmonic

theorem harmonic_iff_bernoulli (P : ProbVec) (ν : Measure Bdry) [IsProbabilityMeasure ν] :
    IsHarmonic P ν ↔ ν = bernoulli P := by
  constructor
  · intro h
    refine BerggrenHarmonic.ext_of_cyl_eq (fun n v => ?_)
    rw [h.cyl_eq n v, BerggrenHarmonic.bernoulli_cyl]
  · rintro rfl
    exact BerggrenHarmonic.bernoulli_isHarmonic P

end BerggrenHarmonic

namespace BerggrenHarmonic

theorem existsUnique_harmonic (P : ProbVec) :
    ∃! ν : Measure Bdry, IsProbabilityMeasure ν ∧ IsHarmonic P ν := by
  refine ⟨bernoulli P, ⟨inferInstance, BerggrenHarmonic.bernoulli_isHarmonic P⟩, ?_⟩
  rintro ν ⟨hprob, hharm⟩
  exact (@BerggrenHarmonic.harmonic_iff_bernoulli P ν hprob).1 hharm

end BerggrenHarmonic

namespace BerggrenHarmonic

theorem bernoulli_uniform_cyl (n : ℕ) (v : Bdry) :
    bernoulli uniformVec (cyl n v) = (ENNReal.ofReal (1 / 3)) ^ n := by
  rw [BerggrenHarmonic.bernoulli_cyl]
  simp [wmass, uniformVec]

end BerggrenHarmonic


theorem solution (P : ProbVec) : IsHarmonic P (bernoulli P) := by
  set ν : Measure Bdry := ∑ a : Letter, ENNReal.ofReal (P.p a) • (bernoulli P).map (cons a)
    with hν
  have hval : ∀ (S : Set Bdry), MeasurableSet S →
      ν S = ∑ a : Letter, ENNReal.ofReal (P.p a) * bernoulli P (cons a ⁻¹' S) := by
    intro S hS
    rw [hν, Measure.coe_finset_sum]
    simp only [Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Measure.map_apply (BerggrenHarmonic.measurable_cons a) hS]
  have huniv : ν univ = 1 := by
    rw [hval univ MeasurableSet.univ]
    simp only [Set.preimage_univ, measure_univ, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (P.pos a).le), P.sum_eq, ENNReal.ofReal_one]
  have hprob : IsProbabilityMeasure ν := ⟨huniv⟩
  have hcyl : ∀ n v, bernoulli P (cyl n v) = ν (cyl n v) := by
    intro n v
    rw [BerggrenHarmonic.bernoulli_cyl]
    cases n with
    | zero => rw [BerggrenHarmonic.cyl_zero, BerggrenHarmonic.wmass_zero, huniv]
    | succ n =>
        rw [hval _ (BerggrenHarmonic.measurableSet_cyl (n + 1) v)]
        have hterm : ∀ a : Letter, ENNReal.ofReal (P.p a) * bernoulli P (cons a ⁻¹' cyl (n+1) v)
            = if a = v 0 then ENNReal.ofReal (P.p (v 0)) * wmass P n (tail v) else 0 := by
          intro a
          rw [BerggrenHarmonic.preimage_cons_cyl_succ]
          by_cases ha : a = v 0
          · subst ha
            rw [if_pos rfl, if_pos rfl, BerggrenHarmonic.bernoulli_cyl]
          · simp [ha]
        rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_ite_eq' Finset.univ (v 0)]
        simp [BerggrenHarmonic.wmass_succ]
  exact @BerggrenHarmonic.ext_of_cyl_eq _ _ inferInstance hprob hcyl

#print axioms solution
