-- Prove2me | solution 1 for BanditAlgorithm.ftrl_simplex_exp_weights_regret
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T15:43:16.493362+00:00
-- url     : https://prove2.me/submissions/d75a26a7-4468-4369-864d-64e4baa6c075

import Definitions.Def_OnlineLinearOptimization
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Tactic

open RealInnerProductSpace
open scoped BigOperators

namespace BanditAlgorithm

noncomputable def simplexSoftmax {d : ℕ}
    (c : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => Real.exp (-c i) / ∑ j, Real.exp (-c j))

lemma simplexSoftmax_apply {d : ℕ} (c : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    simplexSoftmax c i = Real.exp (-c i) / ∑ j, Real.exp (-c j) := rfl

lemma simplexSoftmax_mem {d : ℕ} (hd : 0 < d)
    (c : EuclideanSpace ℝ (Fin d)) :
    simplexSoftmax c ∈
      {v : EuclideanSpace ℝ (Fin d) | (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1} := by
  classical
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hZ : 0 < ∑ j : Fin d, Real.exp (-c j) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  constructor
  · intro i
    rw [simplexSoftmax_apply]
    positivity
  · simp only [simplexSoftmax_apply, ← Finset.sum_div]
    exact div_self (ne_of_gt hZ)

lemma simplexSoftmax_pos {d : ℕ} (hd : 0 < d)
    (c : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    0 < simplexSoftmax c i := by
  classical
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hZ : 0 < ∑ j : Fin d, Real.exp (-c j) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  rw [simplexSoftmax_apply]
  positivity

noncomputable def entropyObjective {d : ℕ}
    (c b : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, (b i * c i + (b i * Real.log (b i) - b i))

lemma log_simplexSoftmax {d : ℕ} (hd : 0 < d)
    (c : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    Real.log (simplexSoftmax c i) =
      -c i - Real.log (∑ j, Real.exp (-c j)) := by
  classical
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hZ : 0 < ∑ j : Fin d, Real.exp (-c j) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  rw [simplexSoftmax_apply, Real.log_div (Real.exp_ne_zero _) (ne_of_gt hZ),
    Real.log_exp]

lemma entropyObjective_softmax_eq {d : ℕ} (hd : 0 < d)
    (c : EuclideanSpace ℝ (Fin d)) :
    entropyObjective c (simplexSoftmax c) =
      -Real.log (∑ j, Real.exp (-c j)) - 1 := by
  classical
  have hp := simplexSoftmax_mem hd c
  simp only [entropyObjective, log_simplexSoftmax hd c]
  calc
    _ = ∑ i, (-simplexSoftmax c i *
          Real.log (∑ j, Real.exp (-c j)) - simplexSoftmax c i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ = -Real.log (∑ j, Real.exp (-c j)) - 1 := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2]
        rw [Finset.sum_neg_distrib, hp.2]
        ring

lemma entropyObjective_sub_softmax {d : ℕ} (hd : 0 < d)
    (c b : EuclideanSpace ℝ (Fin d))
    (hb : b ∈ {v : EuclideanSpace ℝ (Fin d) |
      (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1}) :
    entropyObjective c b - entropyObjective c (simplexSoftmax c) =
      ∑ i, simplexSoftmax c i *
        InformationTheory.klFun (b i / simplexSoftmax c i) := by
  classical
  have hp := simplexSoftmax_mem hd c
  have hpp (i : Fin d) : 0 < simplexSoftmax c i := simplexSoftmax_pos hd c i
  have hterm (i : Fin d) :
      simplexSoftmax c i *
          InformationTheory.klFun (b i / simplexSoftmax c i) =
        (b i * c i + (b i * Real.log (b i) - b i)) +
          b i * Real.log (∑ j, Real.exp (-c j)) +
          simplexSoftmax c i := by
    by_cases hbi : b i = 0
    · simp [hbi, InformationTheory.klFun_apply]
    · rw [InformationTheory.klFun_apply,
        Real.log_div hbi (ne_of_gt (hpp i)),
        log_simplexSoftmax hd c i]
      field_simp [ne_of_gt (hpp i)]
      ring
  rw [entropyObjective_softmax_eq hd c]
  simp only [entropyObjective, hterm, Finset.sum_add_distrib,
    ← Finset.sum_mul, hb.2, hp.2]
  ring

lemma entropyObjective_isMinOn_softmax {d : ℕ} (hd : 0 < d)
    (c : EuclideanSpace ℝ (Fin d)) :
    IsMinOn (entropyObjective c)
      {v : EuclideanSpace ℝ (Fin d) | (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1}
      (simplexSoftmax c) := by
  intro b hb
  change entropyObjective c (simplexSoftmax c) ≤ entropyObjective c b
  rw [← sub_nonneg, entropyObjective_sub_softmax hd c b hb]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (simplexSoftmax_pos hd c i).le
      (InformationTheory.klFun_nonneg
        (div_nonneg (hb.1 i) (simplexSoftmax_pos hd c i).le))

lemma entropyObjective_unique_minimizer {d : ℕ} (hd : 0 < d)
    (c q : EuclideanSpace ℝ (Fin d))
    (hq : q ∈ {v : EuclideanSpace ℝ (Fin d) |
      (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1})
    (hmin : IsMinOn (entropyObjective c)
      {v : EuclideanSpace ℝ (Fin d) | (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1} q) :
    q = simplexSoftmax c := by
  classical
  have hp := simplexSoftmax_mem hd c
  have hle := hmin hp
  have hge := entropyObjective_isMinOn_softmax hd c hq
  have heq : entropyObjective c q = entropyObjective c (simplexSoftmax c) :=
    le_antisymm hle hge
  have hsum :
      ∑ i, simplexSoftmax c i *
        InformationTheory.klFun (q i / simplexSoftmax c i) = 0 := by
    rw [← entropyObjective_sub_softmax hd c q hq, heq, sub_self]
  ext i
  have hnonneg (j : Fin d) :
      0 ≤ simplexSoftmax c j *
        InformationTheory.klFun (q j / simplexSoftmax c j) :=
    mul_nonneg (simplexSoftmax_pos hd c j).le
      (InformationTheory.klFun_nonneg
        (div_nonneg (hq.1 j) (simplexSoftmax_pos hd c j).le))
  have hzero :
      simplexSoftmax c i *
        InformationTheory.klFun (q i / simplexSoftmax c i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => hnonneg j)).mp hsum i (Finset.mem_univ i)
  have hkl :
      InformationTheory.klFun (q i / simplexSoftmax c i) = 0 := by
    exact (mul_eq_zero.mp hzero).resolve_left
      (ne_of_gt (simplexSoftmax_pos hd c i))
  have hratio : q i / simplexSoftmax c i = 1 :=
    (InformationTheory.klFun_eq_zero_iff
      (div_nonneg (hq.1 i) (simplexSoftmax_pos hd c i).le)).mp hkl
  exact (div_eq_one_iff_eq (ne_of_gt (simplexSoftmax_pos hd c i))).mp hratio

noncomputable def cumulativeCost {d : ℕ} (η : ℝ)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => η * ∑ s ∈ Finset.range t, y s i)

lemma cumulativeCost_apply {d : ℕ} (η : ℝ)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (i : Fin d) :
    cumulativeCost η y t i = η * ∑ s ∈ Finset.range t, y s i := rfl

lemma entropyObjective_cumulativeCost {d : ℕ} (η : ℝ)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ)
    (b : EuclideanSpace ℝ (Fin d)) :
    entropyObjective (cumulativeCost η y t) b =
      η * ∑ s ∈ Finset.range t, ⟪b, y s⟫ +
        ∑ i, (b i * Real.log (b i) - b i) := by
  classical
  simp only [entropyObjective, cumulativeCost_apply, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    _ = η * ∑ i, ∑ s ∈ Finset.range t, b i * y s i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      calc
        _ = ∑ s ∈ Finset.range t, b i * (η * y s i) := by
          rw [Finset.mul_sum]
        _ = ∑ s ∈ Finset.range t, η * (b i * y s i) := by
          apply Finset.sum_congr rfl
          intro s hs
          ring
        _ = η * ∑ s ∈ Finset.range t, b i * y s i := by
          rw [Finset.mul_sum]
    _ = η * ∑ s ∈ Finset.range t, ∑ i, b i * y s i := by
      congr 1
      rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma ftrl_iterate_eq_softmax {d : ℕ} (hd : 0 < d) (η : ℝ)
    (y a : ℕ → EuclideanSpace ℝ (Fin d))
    (hiter : IsFTRLIterates η
      (fun v : EuclideanSpace ℝ (Fin d) => ∑ i, (v i * Real.log (v i) - v i))
      {v : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ v i}
      {v : EuclideanSpace ℝ (Fin d) | (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1}
      y a) :
    ∀ t, a t = simplexSoftmax (cumulativeCost η y t) := by
  classical
  let S : Set (EuclideanSpace ℝ (Fin d)) :=
    {v : EuclideanSpace ℝ (Fin d) | (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1}
  have hdom :
      ({v : EuclideanSpace ℝ (Fin d) | (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1} ∩
        {v : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ v i}) = S := by
    ext v
    constructor
    · rintro ⟨hv, _⟩
      exact hv
    · intro hv
      exact ⟨hv, hv.1⟩
  intro t
  have hmem : a t ∈ S := by
    cases t with
    | zero =>
        have hm := hiter.init_mem
        rw [hdom] at hm
        exact hm
    | succ t =>
        have hm := hiter.step_mem t
        rw [hdom] at hm
        exact hm
  apply entropyObjective_unique_minimizer hd (cumulativeCost η y t) (a t) hmem
  intro b hb
  change entropyObjective (cumulativeCost η y t) (a t) ≤
    entropyObjective (cumulativeCost η y t) b
  rw [entropyObjective_cumulativeCost, entropyObjective_cumulativeCost]
  cases t with
  | zero =>
      have hm := hiter.init_isMinOn
      rw [hdom] at hm
      have := hm hb
      simpa using this
  | succ t =>
      have hm := hiter.step_isMinOn t
      rw [hdom] at hm
      exact hm hb

lemma exp_neg_le_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  let f : ℝ → ℝ := fun z => 1 - z + z ^ 2 / 2 - Real.exp (-z)
  have hfderiv (z : ℝ) :
      HasDerivAt f (-1 + z + Real.exp (-z)) z := by
    dsimp [f]
    convert (((hasDerivAt_const z 1).sub (hasDerivAt_id z)).add
      (((hasDerivAt_pow 2 z).div_const 2))).sub
        ((Real.hasDerivAt_exp (-z)).comp z (hasDerivAt_neg z)) using 1 <;> ring
  have hfmono : Monotone f := monotone_of_deriv_nonneg
      (fun z => (hfderiv z).differentiableAt)
      (fun z => by
        rw [(hfderiv z).deriv]
        linarith [Real.one_sub_le_exp_neg z])
  have h := hfmono hx
  dsimp [f] at h
  norm_num at h
  linarith

lemma exp_neg_mul_le_linear_quadratic {η x : ℝ}
    (hη : 0 ≤ η) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-η * x) ≤ 1 - η * x + η ^ 2 / 2 := by
  have hchord := convexOn_exp.2 (x := (0 : ℝ)) (y := -η)
    (Set.mem_univ _) (Set.mem_univ _) (sub_nonneg.mpr hx.2) hx.1 (by ring)
  have hquad := exp_neg_le_quadratic hη
  have hηsq : 0 ≤ η ^ 2 := sq_nonneg η
  calc
    Real.exp (-η * x) =
        Real.exp ((1 - x) • (0 : ℝ) + x • (-η)) := by
          congr 1
          simp [smul_eq_mul]
          ring
    _ ≤ (1 - x) • Real.exp 0 + x • Real.exp (-η) := hchord
    _ ≤ (1 - x) * 1 + x * (1 - η + η ^ 2 / 2) := by
          simp only [smul_eq_mul, Real.exp_zero]
          gcongr
          exact hx.1
    _ ≤ 1 - η * x + η ^ 2 / 2 := by
          have hmul := mul_le_mul_of_nonneg_right hx.2 hηsq
          nlinarith

lemma softmax_log_partition_step {d : ℕ} (hd : 0 < d)
    {η : ℝ} (hη : 0 ≤ η)
    (c x : EuclideanSpace ℝ (Fin d))
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    Real.log (∑ i, Real.exp (-(c i + η * x i))) -
        Real.log (∑ i, Real.exp (-c i)) ≤
      -η * ∑ i, simplexSoftmax c i * x i + η ^ 2 / 2 := by
  classical
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let Z : ℝ := ∑ i, Real.exp (-c i)
  let M : ℝ := ∑ i, simplexSoftmax c i * Real.exp (-η * x i)
  have hZ : 0 < Z :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hp := simplexSoftmax_mem hd c
  have hM : 0 < M := by
    dsimp [M]
    exact Finset.sum_pos
      (fun i _ => mul_pos (simplexSoftmax_pos hd c i) (Real.exp_pos _))
      Finset.univ_nonempty
  have hfactor :
      ∑ i, Real.exp (-(c i + η * x i)) = Z * M := by
    dsimp [Z, M]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [simplexSoftmax_apply]
    field_simp [ne_of_gt hZ]
    rw [← Real.exp_add]
    congr 1
    ring
  have hMupper : M ≤ 1 - η * ∑ i, simplexSoftmax c i * x i + η ^ 2 / 2 := by
    calc
      M ≤ ∑ i, simplexSoftmax c i *
          (1 - η * x i + η ^ 2 / 2) := by
            dsimp [M]
            exact Finset.sum_le_sum fun i hi =>
              mul_le_mul_of_nonneg_left
                (exp_neg_mul_le_linear_quadratic hη (hx i)) (hp.1 i)
      _ = 1 - η * ∑ i, simplexSoftmax c i * x i + η ^ 2 / 2 := by
            calc
              _ = ∑ i, (simplexSoftmax c i -
                    η * (simplexSoftmax c i * x i) +
                    simplexSoftmax c i * (η ^ 2 / 2)) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
              _ = _ := by
                    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                      ← Finset.sum_mul, hp.2]
                    rw [← Finset.mul_sum]
                    ring
  calc
    Real.log (∑ i, Real.exp (-(c i + η * x i))) - Real.log (∑ i, Real.exp (-c i)) =
        Real.log M := by
          rw [hfactor, Real.log_mul (ne_of_gt hZ) (ne_of_gt hM)]
          change Real.log Z + Real.log M - Real.log Z = Real.log M
          ring
    _ ≤ M - 1 := Real.log_le_sub_one_of_pos hM
    _ ≤ -η * ∑ i, simplexSoftmax c i * x i + η ^ 2 / 2 := by
          linarith

noncomputable def logPartition {d : ℕ} (η : ℝ)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) : ℝ :=
  Real.log (∑ i, Real.exp (-(cumulativeCost η y t i)))

lemma cumulativeCost_succ {d : ℕ} (η : ℝ)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (i : Fin d) :
    cumulativeCost η y (t + 1) i =
      cumulativeCost η y t i + η * y t i := by
  simp only [cumulativeCost_apply, Finset.sum_range_succ]
  ring

lemma logPartition_step {d : ℕ} (hd : 0 < d)
    {η : ℝ} (hη : 0 ≤ η)
    (y a : ℕ → EuclideanSpace ℝ (Fin d))
    (hy : ∀ t, ∀ i, y t i ∈ Set.Icc (0 : ℝ) 1)
    (ha : ∀ t, a t = simplexSoftmax (cumulativeCost η y t)) (t : ℕ) :
    logPartition η y (t + 1) - logPartition η y t ≤
      -η * ⟪a t, y t⟫ + η ^ 2 / 2 := by
  have h := softmax_log_partition_step hd hη
    (cumulativeCost η y t) (y t) (hy t)
  rw [← ha t] at h
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h ⊢
  simp only [logPartition, cumulativeCost_succ]
  calc
    _ ≤ -η * ∑ i, a t i * y t i + η ^ 2 / 2 := h
    _ = _ := by
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma logPartition_sum_bound {d : ℕ} (hd : 0 < d)
    {η : ℝ} (hη : 0 ≤ η)
    (y a : ℕ → EuclideanSpace ℝ (Fin d))
    (hy : ∀ t, ∀ i, y t i ∈ Set.Icc (0 : ℝ) 1)
    (ha : ∀ t, a t = simplexSoftmax (cumulativeCost η y t)) (n : ℕ) :
    logPartition η y n - logPartition η y 0 ≤
      -η * ∑ t ∈ Finset.range n, ⟪a t, y t⟫ +
        n * η ^ 2 / 2 := by
  have hsum := Finset.sum_le_sum
    (fun t (_ : t ∈ Finset.range n) =>
      logPartition_step hd hη y a hy ha t)
  rw [Finset.sum_range_sub] at hsum
  calc
    logPartition η y n - logPartition η y 0
        ≤ ∑ t ∈ Finset.range n, (-η * ⟪a t, y t⟫ + η ^ 2 / 2) := hsum
    _ = -η * ∑ t ∈ Finset.range n, ⟪a t, y t⟫ +
          n * η ^ 2 / 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
        ring

lemma logPartition_zero {d : ℕ} (η : ℝ)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) :
    logPartition η y 0 = Real.log d := by
  simp [logPartition, cumulativeCost]

lemma logPartition_comparator_lower {d : ℕ} (hd : 0 < d)
    (η : ℝ) (y : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (a₀ : EuclideanSpace ℝ (Fin d))
    (ha₀ : a₀ ∈ {v : EuclideanSpace ℝ (Fin d) |
      (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1}) :
    -η * ∑ t ∈ Finset.range n, ⟪a₀, y t⟫ ≤
      logPartition η y n := by
  classical
  have ha₀le (i : Fin d) : a₀ i ≤ 1 := by
    calc
      a₀ i ≤ ∑ j, a₀ j :=
        Finset.single_le_sum (fun j _ => ha₀.1 j) (Finset.mem_univ i)
      _ = 1 := ha₀.2
  have hent : ∑ i, (a₀ i * Real.log (a₀ i) - a₀ i) ≤ -1 := by
    calc
      _ ≤ ∑ i, (0 - a₀ i) := by
        exact Finset.sum_le_sum fun i hi => by
          have hlog : Real.log (a₀ i) ≤ 0 :=
            Real.log_nonpos (ha₀.1 i) (ha₀le i)
          have := mul_nonpos_of_nonneg_of_nonpos (ha₀.1 i) hlog
          linarith
      _ = -1 := by rw [Finset.sum_sub_distrib]; simp [ha₀.2]
  have hmin := entropyObjective_isMinOn_softmax hd
    (cumulativeCost η y n) ha₀
  change entropyObjective (cumulativeCost η y n)
      (simplexSoftmax (cumulativeCost η y n)) ≤
    entropyObjective (cumulativeCost η y n) a₀ at hmin
  rw [entropyObjective_softmax_eq hd, entropyObjective_cumulativeCost] at hmin
  rw [logPartition]
  have hcost :
      η * ∑ t ∈ Finset.range n, ⟪a₀, y t⟫ +
          ∑ i, (a₀ i * Real.log (a₀ i) - a₀ i) ≤
        η * ∑ t ∈ Finset.range n, ⟪a₀, y t⟫ - 1 := by
    linarith
  linarith

lemma ftrl_simplex_exp_weights_regret_general
    {d n : ℕ} {η : ℝ} (hd : 0 < d) (hη : 0 < η)
    (y a : ℕ → EuclideanSpace ℝ (Fin d))
    (hy : ∀ t, ∀ i, y t i ∈ Set.Icc (0 : ℝ) 1)
    (hiter : IsFTRLIterates η
      (fun v : EuclideanSpace ℝ (Fin d) => ∑ i, (v i * Real.log (v i) - v i))
      {v : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ v i}
      {v : EuclideanSpace ℝ (Fin d) | (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1}
      y a) :
    ∀ a₀ ∈ {v : EuclideanSpace ℝ (Fin d) |
        (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1},
      oloRegret a y n a₀ ≤ Real.log d / η + n * η / 2 := by
  classical
  intro a₀ ha₀
  have ha := ftrl_iterate_eq_softmax hd η y a hiter
  have hu := logPartition_sum_bound hd hη.le y a hy ha n
  rw [logPartition_zero] at hu
  have hl := logPartition_comparator_lower hd η y n a₀ ha₀
  have hreg :
      oloRegret a y n a₀ =
        (∑ t ∈ Finset.range n, ⟪a t, y t⟫) -
          ∑ t ∈ Finset.range n, ⟪a₀, y t⟫ := by
    simp only [oloRegret, inner_sub_left, Finset.sum_sub_distrib]
  have hcore :
      η * oloRegret a y n a₀ ≤ Real.log d + n * η ^ 2 / 2 := by
    rw [hreg]
    nlinarith
  rw [show Real.log d / η + n * η / 2 =
      (Real.log d + n * η ^ 2 / 2) / η by
        field_simp [ne_of_gt hη]]
  exact (le_div_iff₀ hη).2 (by simpa [mul_comm] using hcore)

end BanditAlgorithm

open BanditAlgorithm

theorem solution
    (d n : ℕ) (y a : ℕ → EuclideanSpace ℝ (Fin d))
    (hy : ∀ t, ∀ i, y t i ∈ Set.Icc (0 : ℝ) 1)
    (hiter : IsFTRLIterates (Real.sqrt (2 * Real.log d / n))
      (fun v : EuclideanSpace ℝ (Fin d) => ∑ i, (v i * Real.log (v i) - v i))
      {v : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ v i}
      {v : EuclideanSpace ℝ (Fin d) | (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1}
      y a) :
    ∀ a₀ ∈ {v : EuclideanSpace ℝ (Fin d) | (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1},
      oloRegret a y n a₀ ≤ Real.sqrt (2 * n * Real.log d) := by
  classical
  intro a₀ ha₀
  by_cases hn : n = 0
  · subst n
    simp [oloRegret]
  by_cases hd0 : d = 0
  · subst d
    simp at ha₀
  by_cases hd1 : d = 1
  · subst d
    have ha_mem (t : ℕ) :
        a t ∈ {v : EuclideanSpace ℝ (Fin 1) |
          (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1} := by
      cases t with
      | zero => exact hiter.init_mem.1
      | succ t => exact (hiter.step_mem t).1
    have ha_eq (t : ℕ) : a t = a₀ := by
      ext i
      fin_cases i
      have hat := (ha_mem t).2
      have ha₀t := ha₀.2
      simpa using hat.trans ha₀t.symm
    simp [oloRegret, ha_eq]
  have hd2 : 2 ≤ d := by omega
  have hdpos : 0 < d := by omega
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hlog : 0 < Real.log d := Real.log_pos (by exact_mod_cast hd2)
  let η : ℝ := Real.sqrt (2 * Real.log d / n)
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hgen := ftrl_simplex_exp_weights_regret_general
    (n := n) (η := η) hdpos hη y a hy hiter a₀ ha₀
  have hηsq : η ^ 2 = 2 * Real.log d / n := by
    dsimp [η]
    rw [Real.sq_sqrt]
    positivity
  have hηsq_mul : η ^ 2 * (n : ℝ) = 2 * Real.log d := by
    calc
      η ^ 2 * (n : ℝ) = (2 * Real.log d / n) * n := by rw [hηsq]
      _ = 2 * Real.log d := by field_simp [Nat.cast_ne_zero.mpr hn]
  have hbalance : Real.log d / η = (n : ℝ) * η / 2 := by
    field_simp [ne_of_gt hη, Nat.cast_ne_zero.mpr hn]
    nlinarith [hηsq_mul]
  have hsqrt_sq :
      (Real.sqrt (2 * n * Real.log d)) ^ 2 = 2 * n * Real.log d := by
    rw [Real.sq_sqrt]
    positivity
  have hscaled_sq :
      ((n : ℝ) * η) ^ 2 = 2 * n * Real.log d := by
    rw [mul_pow, hηsq]
    field_simp [Nat.cast_ne_zero.mpr hn]
  have hscaled :
      (n : ℝ) * η = Real.sqrt (2 * n * Real.log d) := by
    apply (sq_eq_sq₀ (mul_nonneg (Nat.cast_nonneg _) hη.le)
      (Real.sqrt_nonneg _)).mp
    rw [hscaled_sq, hsqrt_sq]
  calc
    oloRegret a y n a₀ ≤ Real.log d / η + n * η / 2 := hgen
    _ = (n : ℝ) * η := by rw [hbalance]; ring
    _ = Real.sqrt (2 * n * Real.log d) := hscaled
