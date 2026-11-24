-- Prove2me | solution 1 for BerggrenHarmonic.eigenvalue_eq_zero_or_one
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T07:15:46.553192+00:00
-- url     : https://prove2.me/submissions/a4fc8afa-71ae-4e52-8bf5-bc7b89dd2d20

-- Thm stub generated from Bridges/BerggrenTransferSpectrum.lean
import Mathlib
import Definitions.Def_Bridges_BerggrenHarmonicMeasure
import Definitions.Def_Bridges_BerggrenTransferSpectrum

/-!
# The transfer operator of the Berggren walk and its spectrum

The Markov operator of the Berggren random walk acts on functions on the boundary
`Bdry = ℕ → Fin 3` by

`(L f)(x) = p₁ f(1·x) + p₂ f(2·x) + p₃ f(3·x)`,

where `a·x = cons a x` prepends the Berggren move `a`.  This is the operator whose fixed
points are the harmonic functions of the walk and whose invariant measure is the harmonic
measure `bernoulli P` of `Catalog.Bridges.BerggrenHarmonicMeasure`.

The conjecture motivating this cycle was that the *spectral gap* of the Berggren walk is
governed by the silver ratio `1 + √2` of the tree's metric growth.  The results below show
that this is false in a strong and clean way: on the natural core of locally constant
functions (the union of the finite-dimensional spaces `DependsOn n`, which is dense in every
reasonable completion), the transfer operator is **nilpotent modulo constants**.

## Main results

* `transfer_dependsOn` : `L` maps functions of the first `n+1` letters to functions of the
  first `n` letters — the operator strictly decreases the "memory" of a function.
* `iterate_transfer_const` : hence `Lⁿ f` is *constant* for every `f` depending on the first
  `n` letters.  This is the nilpotency statement.
* `eigenvalue_eq_zero_or_one` : consequently every eigenvalue of `L` on locally constant
  functions is `0` or `1`, and (`eigenfunction_one_isConst`) the eigenvalue `1` has only the
  constants as eigenfunctions.  The **spectral gap is `1`, independently of `(p₁,p₂,p₃)`**.
* `log_silver_not_eigenvalue` : in particular `log(1+√2)` — the growth exponent of the
  Berggren tree — is *not* an eigenvalue of the Markov operator: the conjectured
  silver-ratio spectral gap is refuted.  (`log_silver_pos_lt_one` isolates the numerical
  fact `0 < log(1+√2) < 1` on which the refutation rests.)
-/

open BerggrenHarmonic

open Finset









/-! ## The spectrum on locally constant functions -/

open MeasureTheory Set MeasurableSpace
open scoped ENNReal
open Finset
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

namespace BerggrenHarmonic

lemma dependsOn_zero_iff (f : Bdry → ℝ) : DependsOn 0 f ↔ ∀ x y, f x = f y := by
  constructor
  · intro h x y; exact h x y (fun i hi => absurd hi (Nat.not_lt_zero i))
  · intro h x y _; exact h x y

end BerggrenHarmonic

namespace BerggrenHarmonic

lemma dependsOn_mono {m n : ℕ} {f : Bdry → ℝ} (hmn : m ≤ n) (hf : DependsOn m f) :
    DependsOn n f :=
  fun x y hxy => hf x y (fun i hi => hxy i (lt_of_lt_of_le hi hmn))

end BerggrenHarmonic

namespace BerggrenHarmonic

@[simp] lemma transfer_const (P : ProbVec) (c : ℝ) :
    transfer P (fun _ => c) = fun _ => c := by
  funext x
  simp only [transfer, ← Finset.sum_mul]
  rw [P.sum_eq, one_mul]

end BerggrenHarmonic

namespace BerggrenHarmonic

theorem transfer_dependsOn (P : ProbVec) {n : ℕ} {f : Bdry → ℝ} (hf : DependsOn (n + 1) f) :
    DependsOn n (transfer P f) := by
  intro x y hxy
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine hf _ _ fun i hi => ?_
  cases i with
  | zero => rfl
  | succ k => exact hxy k (by omega)

end BerggrenHarmonic

namespace BerggrenHarmonic

theorem iterate_transfer_dependsOn_zero (P : ProbVec) :
    ∀ (n : ℕ) (f : Bdry → ℝ), DependsOn n f → DependsOn 0 ((transfer P)^[n] f) := by
  intro n
  induction n with
  | zero => intro f hf; simpa using hf
  | succ n ih =>
      intro f hf
      rw [Function.iterate_succ_apply]
      exact ih _ (BerggrenHarmonic.transfer_dependsOn P hf)

end BerggrenHarmonic

namespace BerggrenHarmonic

theorem iterate_transfer_const (P : ProbVec) {n : ℕ} {f : Bdry → ℝ} (hf : DependsOn n f) :
    ∃ c : ℝ, (transfer P)^[n] f = fun _ => c := by
  refine ⟨(transfer P)^[n] f (fun _ => 0), ?_⟩
  funext x
  exact (BerggrenHarmonic.dependsOn_zero_iff _).1 (BerggrenHarmonic.iterate_transfer_dependsOn_zero P n f hf) x _

end BerggrenHarmonic

namespace BerggrenHarmonic

lemma iterate_transfer_smul (P : ProbVec) {f : Bdry → ℝ} {c : ℝ}
    (hc : transfer P f = fun x => c * f x) :
    ∀ n : ℕ, (transfer P)^[n] f = fun x => c ^ n * f x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      funext x
      have : transfer P (fun x => c ^ n * f x) = fun x => c ^ n * (transfer P f) x := by
        funext y
        simp only [transfer, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [this, hc]
      ring

end BerggrenHarmonic

namespace BerggrenHarmonic

theorem eigenfunction_one_isConst (P : ProbVec) {n : ℕ} {f : Bdry → ℝ} (hf : DependsOn n f)
    (hc : transfer P f = fun x => 1 * f x) : ∀ x y, f x = f y := by
  obtain ⟨c, hconst⟩ := BerggrenHarmonic.iterate_transfer_const P hf
  have h := BerggrenHarmonic.iterate_transfer_smul P hc n
  rw [hconst] at h
  intro x y
  have hx := congrFun h x
  have hy := congrFun h y
  simp only [one_pow, one_mul] at hx hy
  rw [← hx, ← hy]

end BerggrenHarmonic

namespace BerggrenHarmonic

theorem eigenvalue_eq_zero_or_one (P : ProbVec) {n : ℕ} {f : Bdry → ℝ} (hf : DependsOn n f)
    {c : ℝ} (hc : transfer P f = fun x => c * f x) (hne : ∃ x, f x ≠ 0) :
    c = 0 ∨ c = 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hc0, hc1⟩ := hcon
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨K, hK⟩ := BerggrenHarmonic.iterate_transfer_const P hf
  have hiter := BerggrenHarmonic.iterate_transfer_smul P hc n
  rw [hK] at hiter
  -- `f` is constant, because `cⁿ f` is
  have hconst : ∀ x y, f x = f y := by
    intro x y
    have hx := congrFun hiter x
    have hy := congrFun hiter y
    have hcn : c ^ n ≠ 0 := pow_ne_zero n hc0
    have : c ^ n * f x = c ^ n * f y := by rw [← hx, ← hy]
    exact mul_left_cancel₀ hcn this
  -- a constant function is fixed by `L`
  have hfix : transfer P f = f := by
    funext x
    simp only [transfer]
    have : ∀ a : Letter, P.p a * f (cons a x) = P.p a * f x :=
      fun a => by rw [hconst (cons a x) x]
    rw [Finset.sum_congr rfl (fun a _ => this a), ← Finset.sum_mul, P.sum_eq, one_mul]
  have := congrFun (hfix.symm.trans hc) x₀
  have hcx : (c - 1) * f x₀ = 0 := by linarith [this]
  rcases mul_eq_zero.1 hcx with h | h
  · exact hc1 (by linarith)
  · exact hx₀ h

end BerggrenHarmonic

namespace BerggrenHarmonic

theorem log_silver_pos_lt_one :
    0 < Real.log (1 + Real.sqrt 2) ∧ Real.log (1 + Real.sqrt 2) < 1 := by
  have h2 : Real.sqrt 2 < 1.5 := by
    have : Real.sqrt 2 < Real.sqrt 2.25 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    have h225 : Real.sqrt 2.25 = 1.5 := by
      rw [show (2.25 : ℝ) = 1.5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h225 ▸ this]
  have hpos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  constructor
  · exact Real.log_pos (by linarith)
  · have he : (1 : ℝ) + Real.sqrt 2 < Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    calc Real.log (1 + Real.sqrt 2) < Real.log (Real.exp 1) :=
          Real.log_lt_log (by linarith) he
      _ = 1 := Real.log_exp 1

end BerggrenHarmonic

namespace BerggrenHarmonic

theorem log_silver_not_eigenvalue (P : ProbVec) {n : ℕ} {f : Bdry → ℝ} (hf : DependsOn n f)
    (hc : transfer P f = fun x => Real.log (1 + Real.sqrt 2) * f x) : ∀ x, f x = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hlow, hhigh⟩ := BerggrenHarmonic.log_silver_pos_lt_one
  rcases BerggrenHarmonic.eigenvalue_eq_zero_or_one P hf hc hcon with h | h
  · exact absurd h (ne_of_gt hlow)
  · exact absurd h (ne_of_lt hhigh)

end BerggrenHarmonic


theorem solution (P : ProbVec) {n : ℕ} {f : Bdry → ℝ} (hf : DependsOn n f)
    {c : ℝ} (hc : transfer P f = fun x => c * f x) (hne : ∃ x, f x ≠ 0) :
    c = 0 ∨ c = 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hc0, hc1⟩ := hcon
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨K, hK⟩ := BerggrenHarmonic.iterate_transfer_const P hf
  have hiter := BerggrenHarmonic.iterate_transfer_smul P hc n
  rw [hK] at hiter
  -- `f` is constant, because `cⁿ f` is
  have hconst : ∀ x y, f x = f y := by
    intro x y
    have hx := congrFun hiter x
    have hy := congrFun hiter y
    have hcn : c ^ n ≠ 0 := pow_ne_zero n hc0
    have : c ^ n * f x = c ^ n * f y := by rw [← hx, ← hy]
    exact mul_left_cancel₀ hcn this
  -- a constant function is fixed by `L`
  have hfix : transfer P f = f := by
    funext x
    simp only [transfer]
    have : ∀ a : Letter, P.p a * f (cons a x) = P.p a * f x :=
      fun a => by rw [hconst (cons a x) x]
    rw [Finset.sum_congr rfl (fun a _ => this a), ← Finset.sum_mul, P.sum_eq, one_mul]
  have := congrFun (hfix.symm.trans hc) x₀
  have hcx : (c - 1) * f x₀ = 0 := by linarith [this]
  rcases mul_eq_zero.1 hcx with h | h
  · exact hc1 (by linarith)
  · exact hx₀ h

#print axioms solution
