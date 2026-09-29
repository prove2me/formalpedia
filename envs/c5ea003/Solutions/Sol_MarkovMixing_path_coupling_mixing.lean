-- Prove2me | solution 1 for MarkovMixing.path_coupling_mixing
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T18:07:16.012972+00:00
-- url     : https://prove2.me/submissions/81a5732a-062d-4ea5-b817-d26fc0d06143

import Definitions.Def_mm_transport
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_MarkovMixing_path_coupling
import Theorems.Thm_MarkovMixing_tv_coupling

/-!
# Mixing time from path coupling (LPW Corollary 14.7)

Two consequences of the one-step contraction supplied by `path_coupling`.

* Iterating the contraction `t` times and starting from `δ_x` and `π` gives
  `W(P^t(x,·), π) ≤ e^{-αt} W(δ_x, π) ≤ e^{-αt} diam`, and the total-variation
  distance is dominated by the transportation distance because the path metric
  is `≥ 1` off the diagonal (`tv_coupling`).  Taking the supremum over `x`
  bounds `d(t)`.
* Solving `e^{-αt} diam ≤ ε` for `t` gives the mixing-time bound; the ceiling
  `⌈(−log ε + log diam)/α⌉₊` is a witness for the set whose infimum is
  `t_mix(ε)`.  The degenerate case `diam = 0` (a one-point space) is handled
  separately, since there `d(t) ≤ 0 ≤ ε` outright.
-/

namespace MarkovMixing

open scoped BigOperators

private lemma prod_isCoupling {V : Type*} [Fintype V] [DecidableEq V]
    {μ ν : V → ℝ} (hμ : IsDist μ) (hν : IsDist ν) :
    IsCoupling μ ν (fun p : V × V => μ p.1 * ν p.2) := by
  refine ⟨⟨fun p => mul_nonneg (hμ.1 _) (hν.1 _), ?_⟩, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hν.2, mul_one, hμ.2]
  · intro x
    simp only [← Finset.mul_sum, hν.2, mul_one]
  · intro y
    simp only [← Finset.sum_mul, hμ.2, one_mul]

private lemma tdist_bddBelow {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : V → V → ℝ) (hρ0 : ∀ x y : V, 0 ≤ ρ x y) (μ ν : V → ℝ) :
    BddBelow {e : ℝ | ∃ q : V × V → ℝ, IsCoupling μ ν q ∧
      e = ∑ p : V × V, ρ p.1 p.2 * q p} := by
  refine ⟨0, ?_⟩
  rintro e ⟨q, hq, rfl⟩
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hρ0 _ _) (hq.1.1 p)

private lemma tdist_le_cost {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : V → V → ℝ) (hρ0 : ∀ x y : V, 0 ≤ ρ x y) {μ ν : V → ℝ}
    {q : V × V → ℝ} (hq : IsCoupling μ ν q) :
    transportDist ρ μ ν ≤ ∑ p : V × V, ρ p.1 p.2 * q p :=
  csInf_le (tdist_bddBelow ρ hρ0 μ ν) ⟨q, hq, rfl⟩

/-- Any two distributions are within the diameter in transportation distance. -/
private lemma tdist_le_diam {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : V → V → ℝ) (hρ0 : ∀ x y : V, 0 ≤ ρ x y) (D : ℝ)
    (hD : ∀ x y : V, ρ x y ≤ D) {μ ν : V → ℝ} (hμ : IsDist μ) (hν : IsDist ν) :
    transportDist ρ μ ν ≤ D := by
  refine le_trans (tdist_le_cost ρ hρ0 (prod_isCoupling hμ hν)) ?_
  have hb : ∑ p : V × V, ρ p.1 p.2 * (μ p.1 * ν p.2)
      ≤ ∑ p : V × V, D * (μ p.1 * ν p.2) :=
    Finset.sum_le_sum fun p _ =>
      mul_le_mul_of_nonneg_right (hD p.1 p.2) (mul_nonneg (hμ.1 _) (hν.1 _))
  refine le_trans hb ?_
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, hν.2, mul_one, hμ.2]
  simp

/-- `tv ≤ transportDist` whenever `ρ ≥ 1` off the diagonal. -/
private lemma tv_le_tdist {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : V → V → ℝ) (hρ0 : ∀ x y : V, 0 ≤ ρ x y)
    (hρ1 : ∀ x y : V, x ≠ y → 1 ≤ ρ x y) {μ ν : V → ℝ}
    (hμ : IsDist μ) (hν : IsDist ν) : tvDist μ ν ≤ transportDist ρ μ ν := by
  classical
  refine le_csInf ⟨_, ⟨_, prod_isCoupling hμ hν, rfl⟩⟩ ?_
  rintro e ⟨q, hq, rfl⟩
  refine le_trans ((tv_coupling μ ν hμ hν).1 q hq) ?_
  have h1 : ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 ≠ p.2), q p
      ≤ ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 ≠ p.2), ρ p.1 p.2 * q p := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    exact le_mul_of_one_le_left (hq.1.1 p) (hρ1 _ _ hne)
  refine le_trans h1 ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro p _ _
  exact mul_nonneg (hρ0 _ _) (hq.1.1 p)

private lemma vecMul_isDist {V : Type*} [Fintype V] [DecidableEq V]
    {P : Matrix V V ℝ} (hP : IsStochastic P) {μ : V → ℝ} (hμ : IsDist μ) :
    IsDist (Matrix.vecMul μ P) := by
  refine ⟨fun j => ?_, ?_⟩
  · simp only [Matrix.vecMul, dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hμ.1 i) (hP.1 i j)
  · simp only [Matrix.vecMul, dotProduct]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hP.2, mul_one]
    exact hμ.2

private lemma vecMul_pow_stationary {V : Type*} [Fintype V] [DecidableEq V]
    {P : Matrix V V ℝ} {π : V → ℝ} (hπ : IsStationary P π) (t : ℕ) :
    Matrix.vecMul π (P ^ t) = π := by
  induction t with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]

private lemma vecMul_delta {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (t : ℕ) (x : V) :
    Matrix.vecMul (fun y : V => if y = x then (1 : ℝ) else 0) (P ^ t) = rowDist P t x := by
  funext j
  simp [Matrix.vecMul, dotProduct, rowDist]

private lemma delta_isDist {V : Type*} [Fintype V] [DecidableEq V] (x : V) :
    IsDist (fun y : V => if y = x then (1 : ℝ) else 0) := by
  constructor
  · intro y
    by_cases h : y = x <;> simp [h]
  · simp

private lemma walkLength_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ℓ : V → V → ℝ} (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y)
    {x y : V} (w : G.Walk x y) : 0 ≤ walkLength ℓ w := by
  refine List.sum_nonneg ?_
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨d, _, rfl⟩ := ha
  exact le_trans zero_le_one (hℓ1 _ _ d.adj)

private lemma one_le_walkLength {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ℓ : V → V → ℝ} (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y)
    {x y : V} (w : G.Walk x y) (hxy : x ≠ y) : 1 ≤ walkLength ℓ w := by
  cases w with
  | nil => exact absurd rfl hxy
  | cons h p =>
      have h1 : (1 : ℝ) ≤ ℓ _ _ := hℓ1 _ _ h
      have h2 : 0 ≤ walkLength ℓ p := walkLength_nonneg hℓ1 p
      simp only [walkLength, SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons]
      simp only [walkLength] at h2
      linarith

private lemma pathSet_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hconn : G.Connected) (ℓ : V → V → ℝ) (x y : V) :
    {r : ℝ | ∃ w : G.Walk x y, r = walkLength ℓ w}.Nonempty := by
  obtain ⟨w⟩ := hconn.preconnected x y
  exact ⟨walkLength ℓ w, w, rfl⟩

private lemma pathSet_bddBelow {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ℓ : V → V → ℝ} (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y) (x y : V) :
    BddBelow {r : ℝ | ∃ w : G.Walk x y, r = walkLength ℓ w} := by
  refine ⟨0, ?_⟩
  rintro r ⟨w, rfl⟩
  exact walkLength_nonneg hℓ1 w

private lemma pathMetric_le {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ℓ : V → V → ℝ} (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y)
    {x y : V} (w : G.Walk x y) : pathMetric G ℓ x y ≤ walkLength ℓ w :=
  csInf_le (pathSet_bddBelow hℓ1 x y) ⟨w, rfl⟩

private lemma pathMetric_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ℓ : V → V → ℝ} (hconn : G.Connected)
    (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y) (x y : V) : 0 ≤ pathMetric G ℓ x y := by
  refine le_csInf (pathSet_nonempty hconn ℓ x y) ?_
  rintro r ⟨w, rfl⟩
  exact walkLength_nonneg hℓ1 w


private lemma one_le_pathMetric {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ℓ : V → V → ℝ} (hconn : G.Connected)
    (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y) {x y : V} (hxy : x ≠ y) :
    1 ≤ pathMetric G ℓ x y := by
  refine le_csInf (pathSet_nonempty hconn ℓ x y) ?_
  rintro r ⟨w, rfl⟩
  exact one_le_walkLength hℓ1 w hxy

private lemma vecMul_pow_isDist {V : Type*} [Fintype V] [DecidableEq V]
    {P : Matrix V V ℝ} (hP : IsStochastic P) (t : ℕ) {μ : V → ℝ} (hμ : IsDist μ) :
    IsDist (Matrix.vecMul μ (P ^ t)) := by
  induction t with
  | zero => simpa using hμ
  | succ n ih =>
      rw [pow_succ, ← Matrix.vecMul_vecMul]
      exact vecMul_isDist hP ih

end MarkovMixing

open MarkovMixing

/-- **Corollary 14.7** (LPW). -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π)
    (G : SimpleGraph V) (hconn : G.Connected)
    (ℓ : V → V → ℝ) (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y)
    (hℓsymm : ∀ x y : V, ℓ x y = ℓ y x)
    (α : ℝ) (hα : 0 < α)
    (hedge : ∀ x y : V, G.Adj x y →
      ∃ q : V × V → ℝ, IsCoupling (rowDist P 1 x) (rowDist P 1 y) q ∧
        ∑ p : V × V, q p * pathMetric G ℓ p.1 p.2 ≤ Real.exp (-α) * ℓ x y) :
    (∀ t : ℕ, distStationary P π t ≤
      Real.exp (-α * t) * ⨆ p : V × V, pathMetric G ℓ p.1 p.2) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      (mixingTime P π ε : ℝ) ≤
        ⌈(-Real.log ε + Real.log (⨆ p : V × V, pathMetric G ℓ p.1 p.2)) / α⌉₊ := by
  classical
  have hρ0 : ∀ a b : V, 0 ≤ pathMetric G ℓ a b := fun a b => pathMetric_nonneg hconn hℓ1 a b
  have hρ1 : ∀ a b : V, a ≠ b → 1 ≤ pathMetric G ℓ a b :=
    fun a b h => one_le_pathMetric hconn hℓ1 h
  set D : ℝ := ⨆ p : V × V, pathMetric G ℓ p.1 p.2 with hDdef
  have hbdd : BddAbove (Set.range fun p : V × V => pathMetric G ℓ p.1 p.2) :=
    Set.Finite.bddAbove (Set.finite_range _)
  have hDle : ∀ a b : V, pathMetric G ℓ a b ≤ D := fun a b =>
    le_ciSup (f := fun p : V × V => pathMetric G ℓ p.1 p.2) hbdd (a, b)
  have hD0 : 0 ≤ D :=
    le_trans (hρ0 (Classical.arbitrary V) (Classical.arbitrary V)) (hDle _ _)
  have hiter : ∀ (t : ℕ) (μ ν : V → ℝ), IsDist μ → IsDist ν →
      transportDist (pathMetric G ℓ) (Matrix.vecMul μ (P ^ t)) (Matrix.vecMul ν (P ^ t))
        ≤ Real.exp (-α * t) * transportDist (pathMetric G ℓ) μ ν := by
    intro t
    induction t with
    | zero => intro μ ν _ _; simp
    | succ n ih =>
        intro μ ν hμ hν
        have h1 := path_coupling P hP G hconn ℓ hℓ1 hℓsymm α hα hedge
          (Matrix.vecMul μ (P ^ n)) (Matrix.vecMul ν (P ^ n))
          (vecMul_pow_isDist hP n hμ) (vecMul_pow_isDist hP n hν)
        have h2 := ih μ ν hμ hν
        have hexp : Real.exp (-α * ((n + 1 : ℕ) : ℝ))
            = Real.exp (-α) * Real.exp (-α * (n : ℝ)) := by
          rw [← Real.exp_add]
          push_cast
          ring_nf
        rw [pow_succ, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hexp, mul_assoc]
        exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (le_of_lt (Real.exp_pos _)))
  have part1 : ∀ t : ℕ, distStationary P π t ≤ Real.exp (-α * t) * D := by
    intro t
    simp only [distStationary]
    refine ciSup_le fun x => ?_
    have hdx : IsDist (fun y : V => if y = x then (1 : ℝ) else 0) := delta_isDist x
    have h1 := hiter t _ π hdx hπ.1
    rw [vecMul_delta P t x, vecMul_pow_stationary hπ t] at h1
    have hrd : IsDist (rowDist P t x) := by
      rw [← vecMul_delta P t x]
      exact vecMul_pow_isDist hP t hdx
    have h2 : tvDist (rowDist P t x) π ≤ transportDist (pathMetric G ℓ) (rowDist P t x) π :=
      tv_le_tdist _ hρ0 hρ1 hrd hπ.1
    have h3 : transportDist (pathMetric G ℓ) (fun y : V => if y = x then (1 : ℝ) else 0) π ≤ D :=
      tdist_le_diam _ hρ0 D hDle hdx hπ.1
    calc tvDist (rowDist P t x) π
        ≤ transportDist (pathMetric G ℓ) (rowDist P t x) π := h2
      _ ≤ Real.exp (-α * t) *
            transportDist (pathMetric G ℓ) (fun y : V => if y = x then (1 : ℝ) else 0) π := h1
      _ ≤ Real.exp (-α * t) * D := mul_le_mul_of_nonneg_left h3 (le_of_lt (Real.exp_pos _))
  refine ⟨part1, ?_⟩
  intro ε hε _
  set c : ℕ := ⌈(-Real.log ε + Real.log D) / α⌉₊ with hcdef
  have hd := part1 c
  have hle : Real.exp (-α * (c : ℝ)) * D ≤ ε := by
    rcases eq_or_lt_of_le hD0 with h | h
    · rw [← h, mul_zero]
      exact le_of_lt hε
    · have hceil : (-Real.log ε + Real.log D) / α ≤ (c : ℝ) := Nat.le_ceil _
      rw [div_le_iff₀ hα] at hceil
      have hcomm : (c : ℝ) * α = α * (c : ℝ) := mul_comm _ _
      have hkey : -α * (c : ℝ) + Real.log D ≤ Real.log ε := by
        rw [hcomm] at hceil
        linarith
      have h3 : Real.exp (-α * (c : ℝ)) * D = Real.exp (-α * (c : ℝ) + Real.log D) := by
        rw [Real.exp_add, Real.exp_log h]
      rw [h3]
      calc Real.exp (-α * (c : ℝ) + Real.log D) ≤ Real.exp (Real.log ε) :=
            Real.exp_le_exp.mpr hkey
        _ = ε := Real.exp_log hε
  have hmem : distStationary P π c ≤ ε := le_trans hd hle
  have hfin : mixingTime P π ε ≤ c := Nat.sInf_le hmem
  exact_mod_cast hfin
