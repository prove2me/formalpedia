-- Prove2me | solution 1 for MarkovMixing.path_coupling
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T18:01:00.866546+00:00
-- url     : https://prove2.me/submissions/115888e8-a17b-4b45-b78e-d805d3921dd5

import Definitions.Def_mm_transport
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_MarkovMixing_transport_metric

/-!
# Path coupling (Bubley–Dyer, LPW Theorem 14.6)

If every *edge* of a connected graph structure on the state space admits a
one-step coupling contracting the path metric by `e^{-α}`, then *every* pair of
distributions is contracted by `e^{-α}` in the transportation metric.

The proof has three layers.

1. `pathMetric G ℓ` is a genuine metric: nonnegative, vanishing exactly on the
   diagonal (edge lengths are `≥ 1`, so a nontrivial walk has length `≥ 1`),
   symmetric (reverse the walk) and subadditive (concatenate walks).  This is
   what lets us feed it to `transport_metric`.
2. Chaining the edge hypothesis along a walk with the triangle inequality for
   the transportation distance gives
   `W(P(x,·),P(y,·)) ≤ e^{-α} · length(w)` for every walk `w` from `x` to `y`;
   taking the infimum over walks replaces `length(w)` by `pathMetric x y`.
3. Given an optimal coupling `q` of `(μ,ν)` and optimal couplings `t_{x,y}` of
   the rows, the mixture `Q = ∑_{x,y} q(x,y) t_{x,y}` is a coupling of `μP` and
   `νP` whose cost is `∑_{x,y} q(x,y) W(P(x,·),P(y,·)) ≤ e^{-α} ∑ ρ q`.
-/

namespace MarkovMixing

open scoped BigOperators

private lemma sum_swap_aux {V : Type*} [Fintype V] (g : V → V → ℝ) :
    ∑ a : V, ∑ b : V, g a b = ∑ b : V, ∑ a : V, g a b :=
  Finset.sum_comm

/-! ### The path metric is a metric -/

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

private lemma pathMetric_self {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ℓ : V → V → ℝ} (hconn : G.Connected)
    (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y) (x : V) : pathMetric G ℓ x x = 0 := by
  refine le_antisymm ?_ (pathMetric_nonneg hconn hℓ1 x x)
  have := pathMetric_le hℓ1 (SimpleGraph.Walk.nil : G.Walk x x)
  simpa [walkLength] using this

private lemma pathMetric_eq_zero_iff {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ℓ : V → V → ℝ} (hconn : G.Connected)
    (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y) (x y : V) :
    pathMetric G ℓ x y = 0 ↔ x = y := by
  constructor
  · intro h
    by_contra hne
    have h1 : (1 : ℝ) ≤ pathMetric G ℓ x y := by
      refine le_csInf (pathSet_nonempty hconn ℓ x y) ?_
      rintro r ⟨w, rfl⟩
      exact one_le_walkLength hℓ1 w hne
    linarith
  · rintro rfl
    exact pathMetric_self hconn hℓ1 x

private lemma walkLength_reverse {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ℓ : V → V → ℝ} (hℓsymm : ∀ x y : V, ℓ x y = ℓ y x)
    {x y : V} (w : G.Walk x y) : walkLength ℓ w.reverse = walkLength ℓ w := by
  simp only [walkLength, SimpleGraph.Walk.darts_reverse, List.map_reverse, List.map_map,
    List.sum_reverse]
  congr 1
  refine List.map_congr_left ?_
  intro d _
  exact hℓsymm _ _

private lemma pathMetric_symm {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ℓ : V → V → ℝ} (hℓsymm : ∀ x y : V, ℓ x y = ℓ y x) (x y : V) :
    pathMetric G ℓ x y = pathMetric G ℓ y x := by
  have hsets : {r : ℝ | ∃ w : G.Walk x y, r = walkLength ℓ w}
      = {r : ℝ | ∃ w : G.Walk y x, r = walkLength ℓ w} := by
    ext r
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w.reverse, (walkLength_reverse hℓsymm w).symm⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w.reverse, (walkLength_reverse hℓsymm w).symm⟩
  simp only [pathMetric, hsets]

private lemma walkLength_append {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ℓ : V → V → ℝ} {x y z : V} (w₁ : G.Walk x y) (w₂ : G.Walk y z) :
    walkLength ℓ (w₁.append w₂) = walkLength ℓ w₁ + walkLength ℓ w₂ := by
  simp [walkLength, SimpleGraph.Walk.darts_append]

private lemma pathMetric_triangle {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ℓ : V → V → ℝ} (hconn : G.Connected)
    (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y) (x y z : V) :
    pathMetric G ℓ x z ≤ pathMetric G ℓ x y + pathMetric G ℓ y z := by
  have key : ∀ (w₁ : G.Walk x y) (w₂ : G.Walk y z),
      pathMetric G ℓ x z ≤ walkLength ℓ w₁ + walkLength ℓ w₂ := by
    intro w₁ w₂
    rw [← walkLength_append w₁ w₂]
    exact pathMetric_le hℓ1 _
  have h1 : ∀ w₂ : G.Walk y z,
      pathMetric G ℓ x z - walkLength ℓ w₂ ≤ pathMetric G ℓ x y := by
    intro w₂
    refine le_csInf (pathSet_nonempty hconn ℓ x y) ?_
    rintro r ⟨w₁, rfl⟩
    linarith [key w₁ w₂]
  have h2 : pathMetric G ℓ x z - pathMetric G ℓ x y ≤ pathMetric G ℓ y z := by
    refine le_csInf (pathSet_nonempty hconn ℓ y z) ?_
    rintro r ⟨w₂, rfl⟩
    linarith [h1 w₂]
  linarith

/-! ### Generalities on the transportation distance -/

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

private lemma tdist_self_le {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : V → V → ℝ) (hρ0 : ∀ x y : V, 0 ≤ ρ x y) (hdiag : ∀ x : V, ρ x x = 0)
    (μ : V → ℝ) (hμ : IsDist μ) : transportDist ρ μ μ ≤ 0 := by
  classical
  have hc : IsCoupling μ μ (fun p : V × V => if p.1 = p.2 then μ p.1 else 0) := by
    refine ⟨⟨fun p => ?_, ?_⟩, ?_, ?_⟩
    · by_cases h : p.1 = p.2 <;> simp [h, hμ.1]
    · rw [Fintype.sum_prod_type]
      simpa using hμ.2
    · intro x
      simpa using hμ.1 x
    · intro y
      simp
  refine le_trans (tdist_le_cost ρ hρ0 hc) ?_
  rw [Fintype.sum_prod_type]
  refine le_of_eq ?_
  refine Finset.sum_eq_zero fun x _ => ?_
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases h : x = y
  · subst h; simp [hdiag x]
  · simp [h]

private lemma rowDist_isDist {V : Type*} [Fintype V] [DecidableEq V]
    {P : Matrix V V ℝ} (hP : IsStochastic P) (x : V) : IsDist (rowDist P 1 x) := by
  refine ⟨fun y => ?_, ?_⟩
  · simpa [rowDist] using hP.1 x y
  · simpa [rowDist] using hP.2 x

private lemma sum_swap_gen {A B : Type*} [Fintype A] [Fintype B] (g : A → B → ℝ) :
    ∑ a : A, ∑ b : B, g a b = ∑ b : B, ∑ a : A, g a b :=
  Finset.sum_comm

/-! ### One-step contraction along edges, walks, and arbitrary pairs -/

private lemma edge_bound {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (G : SimpleGraph V) (ℓ : V → V → ℝ) (α : ℝ)
    (hconn : G.Connected) (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y)
    (hedge : ∀ x y : V, G.Adj x y →
      ∃ q : V × V → ℝ, IsCoupling (rowDist P 1 x) (rowDist P 1 y) q ∧
        ∑ p : V × V, q p * pathMetric G ℓ p.1 p.2 ≤ Real.exp (-α) * ℓ x y)
    {x y : V} (h : G.Adj x y) :
    transportDist (pathMetric G ℓ) (rowDist P 1 x) (rowDist P 1 y)
      ≤ Real.exp (-α) * ℓ x y := by
  obtain ⟨q, hq, hcost⟩ := hedge x y h
  refine le_trans (tdist_le_cost _ (fun a b => pathMetric_nonneg hconn hℓ1 a b) hq) ?_
  refine le_trans (le_of_eq ?_) hcost
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

private lemma walk_bound {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (G : SimpleGraph V) (hconn : G.Connected)
    (ℓ : V → V → ℝ) (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y)
    (hℓsymm : ∀ x y : V, ℓ x y = ℓ y x) (α : ℝ)
    (hedge : ∀ x y : V, G.Adj x y →
      ∃ q : V × V → ℝ, IsCoupling (rowDist P 1 x) (rowDist P 1 y) q ∧
        ∑ p : V × V, q p * pathMetric G ℓ p.1 p.2 ≤ Real.exp (-α) * ℓ x y)
    {x y : V} (w : G.Walk x y) :
    transportDist (pathMetric G ℓ) (rowDist P 1 x) (rowDist P 1 y)
      ≤ Real.exp (-α) * walkLength ℓ w := by
  induction w with
  | nil =>
      have h0 : ∀ z : V, walkLength ℓ (SimpleGraph.Walk.nil : G.Walk z z) = 0 :=
        fun _ => by simp [walkLength]
      rw [h0, mul_zero]
      exact tdist_self_le _ (fun a b => pathMetric_nonneg hconn hℓ1 a b)
        (fun a => pathMetric_self hconn hℓ1 a) _ (rowDist_isDist hP _)
  | @cons a b c hab p ih =>
      have htri := (transport_metric (pathMetric G ℓ)
        (fun u v => pathMetric_nonneg hconn hℓ1 u v)
        (fun u v => pathMetric_eq_zero_iff hconn hℓ1 u v)
        (fun u v => pathMetric_symm hℓsymm u v)
        (fun u v z => pathMetric_triangle hconn hℓ1 u v z)
        (rowDist P 1 a) (rowDist P 1 b) (rowDist P 1 c)
        (rowDist_isDist hP a) (rowDist_isDist hP b) (rowDist_isDist hP c)).2
      have he := edge_bound P G ℓ α hconn hℓ1 hedge hab
      have hlen : walkLength ℓ (SimpleGraph.Walk.cons hab p) = ℓ a b + walkLength ℓ p := by
        simp [walkLength, SimpleGraph.Walk.darts_cons]
      rw [hlen, mul_add]
      exact le_trans htri (add_le_add he ih)

private lemma pair_bound {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (G : SimpleGraph V) (hconn : G.Connected)
    (ℓ : V → V → ℝ) (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y)
    (hℓsymm : ∀ x y : V, ℓ x y = ℓ y x) (α : ℝ)
    (hedge : ∀ x y : V, G.Adj x y →
      ∃ q : V × V → ℝ, IsCoupling (rowDist P 1 x) (rowDist P 1 y) q ∧
        ∑ p : V × V, q p * pathMetric G ℓ p.1 p.2 ≤ Real.exp (-α) * ℓ x y)
    (x y : V) :
    transportDist (pathMetric G ℓ) (rowDist P 1 x) (rowDist P 1 y)
      ≤ Real.exp (-α) * pathMetric G ℓ x y := by
  have hc : (0 : ℝ) < Real.exp (-α) := Real.exp_pos _
  have hcne : Real.exp (-α) ≠ 0 := ne_of_gt hc
  have key : transportDist (pathMetric G ℓ) (rowDist P 1 x) (rowDist P 1 y) / Real.exp (-α)
      ≤ pathMetric G ℓ x y := by
    refine le_csInf (pathSet_nonempty hconn ℓ x y) ?_
    rintro r ⟨w, rfl⟩
    rw [div_le_iff₀ hc]
    have hw := walk_bound P hP G hconn ℓ hℓ1 hℓsymm α hedge w
    linarith
  have hid : Real.exp (-α) *
      (transportDist (pathMetric G ℓ) (rowDist P 1 x) (rowDist P 1 y) / Real.exp (-α))
      = transportDist (pathMetric G ℓ) (rowDist P 1 x) (rowDist P 1 y) := by
    field_simp
  calc transportDist (pathMetric G ℓ) (rowDist P 1 x) (rowDist P 1 y)
      = Real.exp (-α) *
          (transportDist (pathMetric G ℓ) (rowDist P 1 x) (rowDist P 1 y) / Real.exp (-α)) :=
        hid.symm
    _ ≤ Real.exp (-α) * pathMetric G ℓ x y := mul_le_mul_of_nonneg_left key (le_of_lt hc)

end MarkovMixing

open MarkovMixing

/-- **Theorem 14.6, path coupling** (Bubley–Dyer; LPW). -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (G : SimpleGraph V) (hconn : G.Connected)
    (ℓ : V → V → ℝ) (hℓ1 : ∀ x y : V, G.Adj x y → 1 ≤ ℓ x y)
    (hℓsymm : ∀ x y : V, ℓ x y = ℓ y x)
    (α : ℝ) (hα : 0 < α)
    (hedge : ∀ x y : V, G.Adj x y →
      ∃ q : V × V → ℝ, IsCoupling (rowDist P 1 x) (rowDist P 1 y) q ∧
        ∑ p : V × V, q p * pathMetric G ℓ p.1 p.2 ≤ Real.exp (-α) * ℓ x y)
    (μ ν : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) :
    transportDist (pathMetric G ℓ) (Matrix.vecMul μ P) (Matrix.vecMul ν P) ≤
      Real.exp (-α) * transportDist (pathMetric G ℓ) μ ν := by
  classical
  have hρ0 : ∀ a b : V, 0 ≤ pathMetric G ℓ a b := fun a b => pathMetric_nonneg hconn hℓ1 a b
  have hρeq : ∀ a b : V, pathMetric G ℓ a b = 0 ↔ a = b :=
    fun a b => pathMetric_eq_zero_iff hconn hℓ1 a b
  have hρs : ∀ a b : V, pathMetric G ℓ a b = pathMetric G ℓ b a :=
    fun a b => pathMetric_symm hℓsymm a b
  have hρt : ∀ a b c : V, pathMetric G ℓ a c ≤ pathMetric G ℓ a b + pathMetric G ℓ b c :=
    fun a b c => pathMetric_triangle hconn hℓ1 a b c
  obtain ⟨q, hq, hqval⟩ :=
    (transport_metric (pathMetric G ℓ) hρ0 hρeq hρs hρt μ ν ν hμ hν hν).1
  have hopt : ∀ x y : V, ∃ t : V × V → ℝ,
      IsCoupling (rowDist P 1 x) (rowDist P 1 y) t ∧
      transportDist (pathMetric G ℓ) (rowDist P 1 x) (rowDist P 1 y)
        = ∑ p : V × V, pathMetric G ℓ p.1 p.2 * t p := fun x y =>
    (transport_metric (pathMetric G ℓ) hρ0 hρeq hρs hρt _ _ _
      (rowDist_isDist hP x) (rowDist_isDist hP y) (rowDist_isDist hP y)).1
  choose t ht htval using hopt
  -- the mixed coupling
  have hQ1 : ∀ u : V, ∑ v : V, (∑ x : V, ∑ y : V, q (x, y) * t x y (u, v))
      = Matrix.vecMul μ P u := by
    intro u
    have e1 : ∑ v : V, ∑ x : V, ∑ y : V, q (x, y) * t x y (u, v)
        = ∑ x : V, ∑ v : V, ∑ y : V, q (x, y) * t x y (u, v) :=
      sum_swap_aux fun v x => ∑ y : V, q (x, y) * t x y (u, v)
    have e2 : ∑ x : V, ∑ v : V, ∑ y : V, q (x, y) * t x y (u, v)
        = ∑ x : V, ∑ y : V, ∑ v : V, q (x, y) * t x y (u, v) :=
      Finset.sum_congr rfl fun x _ => sum_swap_aux fun v y => q (x, y) * t x y (u, v)
    rw [e1, e2]
    have e3 : ∀ x y : V, ∑ v : V, q (x, y) * t x y (u, v) = q (x, y) * P x u := by
      intro x y
      rw [← Finset.mul_sum, (ht x y).2.1 u]
      simp [rowDist]
    simp only [e3]
    have e4 : ∀ x : V, ∑ y : V, q (x, y) * P x u = μ x * P x u := by
      intro x
      rw [← Finset.sum_mul, hq.2.1 x]
    simp only [e4]
    simp [Matrix.vecMul, dotProduct]
  have hQ2 : ∀ v : V, ∑ u : V, (∑ x : V, ∑ y : V, q (x, y) * t x y (u, v))
      = Matrix.vecMul ν P v := by
    intro v
    have e1 : ∑ u : V, ∑ x : V, ∑ y : V, q (x, y) * t x y (u, v)
        = ∑ x : V, ∑ u : V, ∑ y : V, q (x, y) * t x y (u, v) :=
      sum_swap_aux fun u x => ∑ y : V, q (x, y) * t x y (u, v)
    have e2 : ∑ x : V, ∑ u : V, ∑ y : V, q (x, y) * t x y (u, v)
        = ∑ x : V, ∑ y : V, ∑ u : V, q (x, y) * t x y (u, v) :=
      Finset.sum_congr rfl fun x _ => sum_swap_aux fun u y => q (x, y) * t x y (u, v)
    rw [e1, e2]
    have e3 : ∀ x y : V, ∑ u : V, q (x, y) * t x y (u, v) = q (x, y) * P y v := by
      intro x y
      rw [← Finset.mul_sum, (ht x y).2.2 v]
      simp [rowDist]
    simp only [e3]
    rw [sum_swap_aux fun x y => q (x, y) * P y v]
    have e4 : ∀ y : V, ∑ x : V, q (x, y) * P y v = ν y * P y v := by
      intro y
      rw [← Finset.sum_mul, hq.2.2 y]
    simp only [e4]
    simp [Matrix.vecMul, dotProduct]
  have hQsum : ∑ p : V × V, (∑ x : V, ∑ y : V, q (x, y) * t x y p) = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [hQ1]
    simp only [Matrix.vecMul, dotProduct]
    rw [sum_swap_aux fun u x => μ x * P x u]
    simp only [← Finset.mul_sum, hP.2, mul_one]
    exact hμ.2
  have hQcoup : IsCoupling (Matrix.vecMul μ P) (Matrix.vecMul ν P)
      (fun p : V × V => ∑ x : V, ∑ y : V, q (x, y) * t x y p) :=
    ⟨⟨fun p => Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
        mul_nonneg (hq.1.1 _) ((ht x y).1.1 _), hQsum⟩, hQ1, hQ2⟩
  have hcost : ∑ p : V × V,
        pathMetric G ℓ p.1 p.2 * (∑ x : V, ∑ y : V, q (x, y) * t x y p)
      = ∑ x : V, ∑ y : V, q (x, y) *
          transportDist (pathMetric G ℓ) (rowDist P 1 x) (rowDist P 1 y) := by
    have step : ∀ p : V × V,
        pathMetric G ℓ p.1 p.2 * (∑ x : V, ∑ y : V, q (x, y) * t x y p)
        = ∑ x : V, ∑ y : V, q (x, y) * (pathMetric G ℓ p.1 p.2 * t x y p) := by
      intro p
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
    simp only [step]
    have f1 : ∑ p : V × V, ∑ x : V, ∑ y : V,
          q (x, y) * (pathMetric G ℓ p.1 p.2 * t x y p)
        = ∑ x : V, ∑ p : V × V, ∑ y : V,
          q (x, y) * (pathMetric G ℓ p.1 p.2 * t x y p) :=
      sum_swap_gen fun p x => ∑ y : V, q (x, y) * (pathMetric G ℓ p.1 p.2 * t x y p)
    have f2 : ∑ x : V, ∑ p : V × V, ∑ y : V,
          q (x, y) * (pathMetric G ℓ p.1 p.2 * t x y p)
        = ∑ x : V, ∑ y : V, ∑ p : V × V,
          q (x, y) * (pathMetric G ℓ p.1 p.2 * t x y p) :=
      Finset.sum_congr rfl fun x _ =>
        sum_swap_gen fun p y => q (x, y) * (pathMetric G ℓ p.1 p.2 * t x y p)
    rw [f1, f2]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.mul_sum, ← htval x y]
  refine le_trans (tdist_le_cost _ hρ0 hQcoup) ?_
  rw [hcost]
  have hbound : ∑ x : V, ∑ y : V, q (x, y) *
        transportDist (pathMetric G ℓ) (rowDist P 1 x) (rowDist P 1 y)
      ≤ ∑ x : V, ∑ y : V, q (x, y) * (Real.exp (-α) * pathMetric G ℓ x y) :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left
        (pair_bound P hP G hconn ℓ hℓ1 hℓsymm α hedge x y) (hq.1.1 (x, y))
  refine le_trans hbound ?_
  rw [hqval, Fintype.sum_prod_type, Finset.mul_sum]
  refine le_of_eq (Finset.sum_congr rfl fun x _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring
