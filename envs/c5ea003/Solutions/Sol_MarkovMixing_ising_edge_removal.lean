-- Prove2me | solution 1 for MarkovMixing.ising_edge_removal
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T21:01:33.83172+00:00
-- url     : https://prove2.me/submissions/46c731b2-51bb-4209-bfc8-81d98aa688e8

import Definitions.Def_mm_ising
import Theorems.Thm_MarkovMixing_dirichlet_comparison_irreducible
import Theorems.Thm_MarkovMixing_glauber_stationary
import Theorems.Thm_MarkovMixing_eigenvalue_basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

set_option maxHeartbeats 2000000

open scoped BigOperators
open MarkovMixing

namespace Ising

variable {Vv : Type*} [Fintype Vv] [DecidableEq Vv]

/-- The (twice-counted) interaction sum. -/
noncomputable def hamil (G : SimpleGraph Vv) [DecidableRel G.Adj] (σ : Vv → Bool) : ℝ :=
  ∑ v, ∑ w, if G.Adj v w then spin σ v * spin σ w else 0

lemma isingWeight_eq (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ) (σ : Vv → Bool) :
    isingWeight G β σ = Real.exp (β * 2⁻¹ * hamil G σ) := rfl

lemma spin_abs (σ : Vv → Bool) (v : Vv) : |spin σ v| = 1 := by
  unfold spin
  by_cases h : σ v <;> simp [h]

lemma isingWeight_pos (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ) (σ : Vv → Bool) :
    0 < isingWeight G β σ := Real.exp_pos _

lemma partition_pos [Nonempty Vv] (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ) :
    0 < ∑ τ : Vv → Bool, isingWeight G β τ :=
  Finset.sum_pos (fun τ _ => isingWeight_pos G β τ) ⟨fun _ => true, Finset.mem_univ _⟩

lemma isingDist_pos [Nonempty Vv] (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ)
    (σ : Vv → Bool) : 0 < isingDist G β σ :=
  div_pos (isingWeight_pos G β σ) (partition_pos G β)

lemma isingDist_isDist [Nonempty Vv] (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ) :
    IsDist (isingDist G β) := by
  refine ⟨fun σ => (isingDist_pos G β σ).le, ?_⟩
  show ∑ σ : Vv → Bool, isingWeight G β σ / ∑ τ : Vv → Bool, isingWeight G β τ = 1
  rw [← Finset.sum_div]
  exact div_self (partition_pos G β).ne'

/-! ### Counting the ordered pairs across a subgraph relation -/

lemma sum_indicator_degree (D : SimpleGraph Vv) [DecidableRel D.Adj] (v : Vv) :
    ∑ w, (if D.Adj v w then (1 : ℝ) else 0) = (D.degree v : ℝ) := by
  have hset : (Finset.univ.filter fun w => D.Adj v w) = D.neighborFinset v := by
    ext w
    simp [SimpleGraph.mem_neighborFinset]
  simp only [Finset.sum_boole, hset, SimpleGraph.card_neighborFinset_eq_degree]

lemma sum_pairs_indicator (D : SimpleGraph Vv) [DecidableRel D.Adj] :
    ∑ v, ∑ w, (if D.Adj v w then (1 : ℝ) else 0) = 2 * (D.edgeFinset.card : ℝ) := by
  rw [Finset.sum_congr rfl (fun v _ => sum_indicator_degree D v)]
  have h := SimpleGraph.sum_degrees_eq_twice_card_edges D
  exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h

lemma div_le_helper (a b c d E : ℝ) (hb : 0 < b) (hd : 0 < d)
    (h : a * d ≤ E * c * b) : a / b ≤ E * (c / d) := by
  rw [← mul_div_assoc, div_le_div_iff₀ hb hd]
  exact h

/-! ### Comparing the Gibbs weights of `G` and a subgraph `G'` -/

section Compare

variable {G G' : SimpleGraph Vv} [DecidableRel G.Adj] [DecidableRel G'.Adj]

lemma hamil_split (hsub : G' ≤ G) (σ : Vv → Bool) :
    hamil G σ = hamil G' σ
      + ∑ v, ∑ w, (if G.Adj v w ∧ ¬ G'.Adj v w then spin σ v * spin σ w else 0) := by
  unfold hamil
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h1 : G'.Adj v w
  · have h2 : G.Adj v w := hsub h1
    simp [h1, h2]
  · by_cases h2 : G.Adj v w <;> simp [h1, h2]

/-- Counting the ordered pairs that carry a removed edge. -/
lemma pair_count (G G' : SimpleGraph Vv) [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    ∑ v, ∑ w, (if G.Adj v w ∧ ¬ G'.Adj v w then (1 : ℝ) else 0)
      = 2 * ((G.edgeFinset \ G'.edgeFinset).card : ℝ) := by
  classical
  letI : DecidableRel (G \ G').Adj := fun a b =>
    inferInstanceAs (Decidable (G.Adj a b ∧ ¬ G'.Adj a b))
  have hcard : ∀ inst : Fintype (G \ G').edgeSet,
      (@SimpleGraph.edgeFinset Vv (G \ G') inst).card
        = (G.edgeFinset \ G'.edgeFinset).card := by
    intro inst
    congr 1
    ext e
    simp [SimpleGraph.mem_edgeFinset, Finset.mem_sdiff]
  have h := sum_pairs_indicator (G \ G')
  rw [hcard] at h
  rw [← h]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ =>
    if_congr (SimpleGraph.sdiff_adj G G' v w).symm rfl rfl

/-- The removal weight `r = |E(G) \ E(G')|`. -/
noncomputable def rr (G G' : SimpleGraph Vv) [DecidableRel G.Adj] [DecidableRel G'.Adj] : ℝ :=
  ((G.edgeFinset \ G'.edgeFinset).card : ℝ)

lemma rr_nonneg : 0 ≤ rr G G' := by unfold rr; positivity

lemma diff_abs_le (σ : Vv → Bool) :
    |∑ v, ∑ w, (if G.Adj v w ∧ ¬ G'.Adj v w then spin σ v * spin σ w else 0)|
      ≤ 2 * rr G G' := by
  have hbound : ∀ v : Vv,
      |∑ w, (if G.Adj v w ∧ ¬ G'.Adj v w then spin σ v * spin σ w else 0)|
        ≤ ∑ w, (if G.Adj v w ∧ ¬ G'.Adj v w then (1 : ℝ) else 0) := by
    intro v
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun w _ => ?_
    by_cases h : G.Adj v w ∧ ¬ G'.Adj v w
    · rw [if_pos h, if_pos h, abs_mul, spin_abs, spin_abs]
      norm_num
    · simp [h]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun v _ => hbound v) ?_
  rw [pair_count G G', rr]

lemma weight_ratio (hsub : G' ≤ G) {β : ℝ} (hβ : 0 ≤ β) (σ : Vv → Bool) :
    isingWeight G β σ ≤ Real.exp (β * rr G G') * isingWeight G' β σ ∧
    isingWeight G' β σ ≤ Real.exp (β * rr G G') * isingWeight G β σ := by
  set Δh : ℝ := ∑ v, ∑ w, (if G.Adj v w ∧ ¬ G'.Adj v w then spin σ v * spin σ w else 0)
    with hΔ
  have habs : |Δh| ≤ 2 * rr G G' := diff_abs_le σ
  have hW : isingWeight G β σ = Real.exp (β * 2⁻¹ * Δh) * isingWeight G' β σ := by
    rw [isingWeight_eq, isingWeight_eq, ← Real.exp_add, hamil_split hsub σ]
    congr 1
    ring
  have hpos' : (0:ℝ) < isingWeight G' β σ := isingWeight_pos G' β σ
  have hb1 : β * 2⁻¹ * Δh ≤ β * rr G G' := by nlinarith [(abs_le.mp habs).2, hβ]
  have hb2 : -(β * rr G G') ≤ β * 2⁻¹ * Δh := by nlinarith [(abs_le.mp habs).1, hβ]
  refine ⟨?_, ?_⟩
  · rw [hW]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hb1) hpos'.le
  · rw [hW]
    have h1 : (1:ℝ) ≤ Real.exp (β * rr G G') * Real.exp (β * 2⁻¹ * Δh) := by
      rw [← Real.exp_add]
      have := Real.exp_le_exp.mpr (show (0:ℝ) ≤ β * rr G G' + β * 2⁻¹ * Δh by linarith)
      simpa using this
    calc isingWeight G' β σ = 1 * isingWeight G' β σ := (one_mul _).symm
      _ ≤ (Real.exp (β * rr G G') * Real.exp (β * 2⁻¹ * Δh)) * isingWeight G' β σ :=
          mul_le_mul_of_nonneg_right h1 hpos'.le
      _ = Real.exp (β * rr G G') * (Real.exp (β * 2⁻¹ * Δh) * isingWeight G' β σ) := by ring

lemma partition_ratio [Nonempty Vv] (hsub : G' ≤ G) {β : ℝ} (hβ : 0 ≤ β) :
    (∑ τ : Vv → Bool, isingWeight G β τ)
      ≤ Real.exp (β * rr G G') * ∑ τ : Vv → Bool, isingWeight G' β τ ∧
    (∑ τ : Vv → Bool, isingWeight G' β τ)
      ≤ Real.exp (β * rr G G') * ∑ τ : Vv → Bool, isingWeight G β τ := by
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ _ => (weight_ratio hsub hβ τ).1
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ _ => (weight_ratio hsub hβ τ).2

/-- The two Gibbs measures are within a factor `e^{2βr}` of each other. -/
lemma dist_ratio [Nonempty Vv] (hsub : G' ≤ G) {β : ℝ} (hβ : 0 ≤ β) (σ : Vv → Bool) :
    isingDist G β σ ≤ Real.exp (2 * (β * rr G G')) * isingDist G' β σ ∧
    isingDist G' β σ ≤ Real.exp (2 * (β * rr G G')) * isingDist G β σ := by
  have hZ : (0:ℝ) < ∑ τ : Vv → Bool, isingWeight G β τ := partition_pos G β
  have hZ' : (0:ℝ) < ∑ τ : Vv → Bool, isingWeight G' β τ := partition_pos G' β
  have hsq : Real.exp (2 * (β * rr G G'))
      = Real.exp (β * rr G G') * Real.exp (β * rr G G') := by
    rw [← Real.exp_add]; ring_nf
  have hpr := partition_ratio (G := G) (G' := G') hsub hβ
  constructor
  · rw [hsq]
    refine div_le_helper _ _ _ _ _ hZ hZ' ?_
    calc isingWeight G β σ * (∑ τ : Vv → Bool, isingWeight G' β τ)
        ≤ (Real.exp (β * rr G G') * isingWeight G' β σ) *
            (Real.exp (β * rr G G') * ∑ τ : Vv → Bool, isingWeight G β τ) :=
          mul_le_mul (weight_ratio hsub hβ σ).1 hpr.2 hZ'.le
            (mul_nonneg (Real.exp_pos _).le (isingWeight_pos G' β σ).le)
      _ = Real.exp (β * rr G G') * Real.exp (β * rr G G') * isingWeight G' β σ *
            ∑ τ : Vv → Bool, isingWeight G β τ := by ring
  · rw [hsq]
    refine div_le_helper _ _ _ _ _ hZ' hZ ?_
    calc isingWeight G' β σ * (∑ τ : Vv → Bool, isingWeight G β τ)
        ≤ (Real.exp (β * rr G G') * isingWeight G β σ) *
            (Real.exp (β * rr G G') * ∑ τ : Vv → Bool, isingWeight G' β τ) :=
          mul_le_mul (weight_ratio hsub hβ σ).2 hpr.1 hZ.le
            (mul_nonneg (Real.exp_pos _).le (isingWeight_pos G β σ).le)
      _ = Real.exp (β * rr G G') * Real.exp (β * rr G G') * isingWeight G β σ *
            ∑ τ : Vv → Bool, isingWeight G' β τ := by ring

end Compare

/-! ### The single-site conditional distribution -/

section Local

/-- Flip the spin at one site. -/
def flipAt (σ : Vv → Bool) (v : Vv) : Vv → Bool := Function.update σ v (!σ v)

lemma flipAt_apply_self (σ : Vv → Bool) (v : Vv) : flipAt σ v v = !σ v := by
  simp [flipAt]

lemma flipAt_apply_ne (σ : Vv → Bool) (v w : Vv) (h : w ≠ v) : flipAt σ v w = σ w := by
  simp [flipAt, h]

lemma flipAt_ne (σ : Vv → Bool) (v : Vv) : σ ≠ flipAt σ v := by
  intro h
  have h2 := congrFun h v
  rw [flipAt_apply_self] at h2
  cases hb : σ v <;> rw [hb] at h2 <;> simp at h2

lemma agree_set (σ : Vv → Bool) (v : Vv) :
    (Finset.univ.filter (fun z : Vv → Bool => ∀ w : Vv, w ≠ v → z w = σ w))
      = {σ, flipAt σ v} := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hz
    by_cases hv : z v = σ v
    · left
      funext w
      by_cases h : w = v
      · subst h; exact hv
      · exact hz w h
    · right
      funext w
      by_cases h : w = v
      · subst h
        rw [flipAt_apply_self]
        cases hb : σ w <;> cases hc : z w <;> simp_all
      · rw [flipAt_apply_ne σ v w h]
        exact hz w h
  · rintro (rfl | rfl)
    · intro w _; rfl
    · intro w hw; exact flipAt_apply_ne σ v w hw

lemma spin_flip (σ : Vv → Bool) (v w : Vv) :
    spin (flipAt σ v) w = if w = v then -(spin σ v) else spin σ w := by
  by_cases h : w = v
  · subst h
    rw [if_pos rfl]
    unfold spin
    rw [flipAt_apply_self]
    cases hb : σ w <;> simp
  · rw [if_neg h]
    unfold spin
    rw [flipAt_apply_ne σ v w h]

variable {G : SimpleGraph Vv} [DecidableRel G.Adj]

/-- The local field `∑_{w ∼ v} σ(v)σ(w)`. -/
noncomputable def locfield (G : SimpleGraph Vv) [DecidableRel G.Adj]
    (σ : Vv → Bool) (v : Vv) : ℝ :=
  ∑ w, if G.Adj v w then spin σ v * spin σ w else 0

lemma locfield_abs_le (σ : Vv → Bool) (v : Vv) :
    |locfield G σ v| ≤ (G.degree v : ℝ) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun w _ => ?_)) (le_of_eq (sum_indicator_degree G v))
  by_cases h : G.Adj v w
  · rw [if_pos h, if_pos h, abs_mul, spin_abs, spin_abs]
    norm_num
  · simp [h]

lemma hamil_flip (σ : Vv → Bool) (v : Vv) :
    hamil G (flipAt σ v) = hamil G σ - 4 * locfield G σ v := by
  have hloop : ¬ G.Adj v v := by simp
  have key : ∀ a b : Vv, G.Adj a b →
      spin (flipAt σ v) a * spin (flipAt σ v) b
        = spin σ a * spin σ b
          - 2 * (if a = v then spin σ a * spin σ b else 0)
          - 2 * (if b = v then spin σ a * spin σ b else 0) := by
    intro a b hab
    rw [spin_flip, spin_flip]
    by_cases ha : a = v <;> by_cases hb : b = v
    · exfalso; subst ha; subst hb; exact hloop hab
    · rw [if_pos ha, if_neg hb, if_pos ha, if_neg hb]; subst ha; ring
    · rw [if_neg ha, if_pos hb, if_neg ha, if_pos hb]; subst hb; ring
    · rw [if_neg ha, if_neg hb, if_neg ha, if_neg hb]; ring
  have key2 : ∀ a b : Vv,
      (if G.Adj a b then spin (flipAt σ v) a * spin (flipAt σ v) b else 0)
        = (if G.Adj a b then spin σ a * spin σ b else 0)
          - 2 * (if a = v then (if G.Adj a b then spin σ a * spin σ b else 0) else 0)
          - 2 * (if b = v then (if G.Adj a b then spin σ a * spin σ b else 0) else 0) := by
    intro a b
    by_cases hab : G.Adj a b
    · rw [if_pos hab, if_pos hab, key a b hab]
    · simp [hab]
  have hinner : ∀ a : Vv,
      ∑ b, (if G.Adj a b then spin (flipAt σ v) a * spin (flipAt σ v) b else 0)
        = (∑ b, (if G.Adj a b then spin σ a * spin σ b else 0))
          - (∑ b, 2 * (if a = v then (if G.Adj a b then spin σ a * spin σ b else 0) else 0))
          - (∑ b, 2 * (if b = v then (if G.Adj a b then spin σ a * spin σ b else 0) else 0)) := by
    intro a
    rw [Finset.sum_congr rfl (fun b _ => key2 a b)]
    simp only [Finset.sum_sub_distrib]
  unfold hamil
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  simp only [Finset.sum_sub_distrib]
  have hA : ∑ a : Vv, ∑ b : Vv,
      2 * (if a = v then (if G.Adj a b then spin σ a * spin σ b else 0) else 0)
        = 2 * locfield G σ v := by
    have e : ∀ a : Vv, ∑ b : Vv,
        2 * (if a = v then (if G.Adj a b then spin σ a * spin σ b else 0) else 0)
          = if a = v then 2 * locfield G σ v else 0 := by
      intro a
      by_cases ha : a = v
      · subst ha
        simp only [if_pos rfl, ← Finset.mul_sum]
        rfl
      · simp [ha]
    rw [Finset.sum_congr rfl (fun a _ => e a),
      Finset.sum_ite_eq' Finset.univ v (fun _ => 2 * locfield G σ v)]
    simp
  have hB : ∑ a : Vv, ∑ b : Vv,
      2 * (if b = v then (if G.Adj a b then spin σ a * spin σ b else 0) else 0)
        = 2 * locfield G σ v := by
    have e : ∀ a : Vv, ∑ b : Vv,
        2 * (if b = v then (if G.Adj a b then spin σ a * spin σ b else 0) else 0)
          = 2 * (if G.Adj a v then spin σ a * spin σ v else 0) := by
      intro a
      rw [← Finset.mul_sum]
      congr 1
      simpa using Finset.sum_ite_eq' Finset.univ v
        (fun b => if G.Adj a b then spin σ a * spin σ b else 0)
    rw [Finset.sum_congr rfl (fun a _ => e a), ← Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : G.Adj a v
    · rw [if_pos h, if_pos (G.symm h)]; ring
    · rw [if_neg h, if_neg (fun hc => h (G.symm hc))]
  rw [hA, hB]
  ring

lemma weight_flip (β : ℝ) (σ : Vv → Bool) (v : Vv) :
    isingWeight G β (flipAt σ v)
      = isingWeight G β σ * Real.exp (-(2 * β * locfield G σ v)) := by
  rw [isingWeight_eq, isingWeight_eq, ← Real.exp_add, hamil_flip]
  congr 1
  ring

end Local

/-! ### The single-site conditional probability -/

section Cond

variable [Nonempty Vv]

/-- `π(σ)` conditioned on the configuration off `v`. -/
noncomputable def pcond (π : (Vv → Bool) → ℝ) (σ : Vv → Bool) (v : Vv) : ℝ :=
  π σ / (π σ + π (flipAt σ v))

lemma quot_id (a z e : ℝ) (ha : 0 < a) (hz : 0 < z) (he : 0 < e) :
    a / z / (a / z + a * e / z) = 1 / (1 + e) := by
  have h2 : (1:ℝ) + e ≠ 0 := by positivity
  have hane : a ≠ 0 := ha.ne'
  have hzne : z ≠ 0 := hz.ne'
  field_simp

lemma pcond_ising (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ) (σ : Vv → Bool) (v : Vv) :
    pcond (isingDist G β) σ v = 1 / (1 + Real.exp (-(2 * β * locfield G σ v))) := by
  have hZ : (0:ℝ) < ∑ τ : Vv → Bool, isingWeight G β τ := partition_pos G β
  have hW : (0:ℝ) < isingWeight G β σ := isingWeight_pos G β σ
  have hfl := weight_flip (G := G) β σ v
  have he : (0:ℝ) < Real.exp (-(2 * β * locfield G σ v)) := Real.exp_pos _
  show isingWeight G β σ / (∑ τ : Vv → Bool, isingWeight G β τ) /
      (isingWeight G β σ / (∑ τ : Vv → Bool, isingWeight G β τ)
        + isingWeight G β (flipAt σ v) / ∑ τ : Vv → Bool, isingWeight G β τ) = _
  rw [hfl]
  exact quot_id _ _ _ hW hZ he

lemma pcond_pos (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ) (σ : Vv → Bool) (v : Vv) :
    0 < pcond (isingDist G β) σ v := by
  rw [pcond_ising]
  have := Real.exp_pos (-(2 * β * locfield G σ v))
  positivity

lemma pcond_le_of_bound {G : SimpleGraph Vv} [DecidableRel G.Adj] {β Δ : ℝ}
    (hβ : 0 ≤ β) (hΔ : 0 ≤ Δ) (σ : Vv → Bool) (v : Vv)
    (h : |locfield G σ v| ≤ Δ) :
    pcond (isingDist G β) σ v ≤ 1 / (1 + Real.exp (-(2 * β * Δ))) := by
  rw [pcond_ising]
  have hb : -(2 * β * Δ) ≤ -(2 * β * locfield G σ v) := by
    have := (abs_le.mp h).2
    nlinarith
  have h1 : Real.exp (-(2 * β * Δ)) ≤ Real.exp (-(2 * β * locfield G σ v)) :=
    Real.exp_le_exp.mpr hb
  have h2 : (0:ℝ) < 1 + Real.exp (-(2 * β * Δ)) := by positivity
  have h3 : (0:ℝ) < 1 + Real.exp (-(2 * β * locfield G σ v)) := by
    have := Real.exp_pos (-(2 * β * locfield G σ v)); linarith
  exact one_div_le_one_div_of_le h2 (by linarith)

lemma pcond_ge_of_bound {G : SimpleGraph Vv} [DecidableRel G.Adj] {β Δ : ℝ}
    (hβ : 0 ≤ β) (hΔ : 0 ≤ Δ) (σ : Vv → Bool) (v : Vv)
    (h : |locfield G σ v| ≤ Δ) :
    1 / (1 + Real.exp (2 * β * Δ)) ≤ pcond (isingDist G β) σ v := by
  rw [pcond_ising]
  have hb : -(2 * β * locfield G σ v) ≤ 2 * β * Δ := by
    have := (abs_le.mp h).1
    nlinarith
  have h1 : Real.exp (-(2 * β * locfield G σ v)) ≤ Real.exp (2 * β * Δ) :=
    Real.exp_le_exp.mpr hb
  have h3 : (0:ℝ) < 1 + Real.exp (-(2 * β * locfield G σ v)) := by
    have := Real.exp_pos (-(2 * β * locfield G σ v)); linarith
  exact one_div_le_one_div_of_le h3 (by linarith)

/-- The single-site conditional probabilities of two graphs with the same maximal
degree bound differ by at most `e^{2βΔ}`. -/
lemma pcond_ratio {G G' : SimpleGraph Vv} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    {β Δ : ℝ} (hβ : 0 ≤ β) (hΔ : 0 ≤ Δ) (σ : Vv → Bool) (v : Vv)
    (h : |locfield G σ v| ≤ Δ) (h' : |locfield G' σ v| ≤ Δ) :
    pcond (isingDist G' β) σ v ≤ Real.exp (2 * β * Δ) * pcond (isingDist G β) σ v := by
  have hE : (0:ℝ) < Real.exp (2 * β * Δ) := Real.exp_pos _
  have hid : 1 / (1 + Real.exp (-(2 * β * Δ)))
      = Real.exp (2 * β * Δ) * (1 / (1 + Real.exp (2 * β * Δ))) := by
    have hne : Real.exp (2 * β * Δ) ≠ 0 := ne_of_gt hE
    have hne2 : (1:ℝ) + Real.exp (2 * β * Δ) ≠ 0 := by positivity
    rw [Real.exp_neg]
    field_simp
    ring
  calc pcond (isingDist G' β) σ v ≤ 1 / (1 + Real.exp (-(2 * β * Δ))) :=
        pcond_le_of_bound hβ hΔ σ v h'
    _ = Real.exp (2 * β * Δ) * (1 / (1 + Real.exp (2 * β * Δ))) := hid
    _ ≤ Real.exp (2 * β * Δ) * pcond (isingDist G β) σ v :=
        mul_le_mul_of_nonneg_left (pcond_ge_of_bound hβ hΔ σ v h) hE.le

end Cond

/-! ### Irreducibility of the Glauber dynamics -/

section Irr

variable [Nonempty Vv]

lemma normalizer_pos (π : (Vv → Bool) → ℝ) (hpos : ∀ σ, 0 < π σ) (σ : Vv → Bool) (u : Vv) :
    0 < ∑ z ∈ Finset.univ.filter (fun z : Vv → Bool => ∀ w : Vv, w ≠ u → z w = σ w), π z := by
  refine Finset.sum_pos (fun z _ => hpos z) ⟨σ, ?_⟩
  simp

lemma glauber_pos (π : (Vv → Bool) → ℝ) (hpos : ∀ σ, 0 < π σ)
    (σ τ : Vv → Bool) (v : Vv) (h : ∀ w : Vv, w ≠ v → τ w = σ w) :
    0 < glauber π σ τ := by
  have hcard : (0:ℝ) < (Fintype.card Vv : ℝ) := by
    have : 0 < Fintype.card Vv := Fintype.card_pos
    exact_mod_cast this
  show 0 < (Fintype.card Vv : ℝ)⁻¹ * ∑ u : Vv,
    (if ∀ w : Vv, w ≠ u → τ w = σ w then
      π τ / ∑ z ∈ Finset.univ.filter (fun z : Vv → Bool => ∀ w : Vv, w ≠ u → z w = σ w), π z
     else 0)
  refine mul_pos (by positivity) ?_
  refine Finset.sum_pos' (fun u _ => ?_) ⟨v, Finset.mem_univ v, ?_⟩
  · by_cases hu : ∀ w : Vv, w ≠ u → τ w = σ w
    · rw [if_pos hu]
      exact (div_pos (hpos τ) (normalizer_pos π hpos σ u)).le
    · rw [if_neg hu]
  · rw [if_pos h]
    exact div_pos (hpos τ) (normalizer_pos π hpos σ v)

lemma glauber_irreducible (π : (Vv → Bool) → ℝ) (hπ : IsDist π) (hpos : ∀ σ, 0 < π σ) :
    MarkovMixing.Irreducible (glauber π) := by
  classical
  set P : Matrix (Vv → Bool) (Vv → Bool) ℝ := glauber π with hPdef
  have hnn : ∀ σ τ, 0 ≤ P σ τ := fun σ τ => (MarkovMixing.glauber_stationary π hπ).1 σ τ
  have hpownn : ∀ (t : ℕ) (σ τ : Vv → Bool), 0 ≤ (P ^ t) σ τ := by
    intro t
    induction t with
    | zero =>
      intro σ τ
      by_cases h : σ = τ <;> simp [Matrix.one_apply, h]
    | succ t ih =>
      intro σ τ
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun z _ => mul_nonneg (ih σ z) (hnn z τ)
  have hkey : ∀ (S : Finset Vv) (σ τ : Vv → Bool),
      0 < (P ^ S.card) σ (fun w => if w ∈ S then τ w else σ w) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro σ τ
      have he : (fun w => if w ∈ (∅ : Finset Vv) then τ w else σ w) = σ := by
        funext w; simp
      rw [he]
      simp [Matrix.one_apply]
    | insert v S hv ih =>
      intro σ τ
      set y : Vv → Bool := fun w => if w ∈ S then τ w else σ w with hy
      set z : Vv → Bool := fun w => if w ∈ insert v S then τ w else σ w with hz
      have hzy : ∀ w : Vv, w ≠ v → z w = y w := by
        intro w hw
        show (if w ∈ insert v S then τ w else σ w) = if w ∈ S then τ w else σ w
        by_cases hs : w ∈ S
        · rw [if_pos (Finset.mem_insert_of_mem hs), if_pos hs]
        · have : w ∉ insert v S := by
            intro hc
            rcases Finset.mem_insert.mp hc with h1 | h1
            · exact hw h1
            · exact hs h1
          rw [if_neg this, if_neg hs]
      rw [Finset.card_insert_of_notMem hv, pow_succ, Matrix.mul_apply]
      refine Finset.sum_pos' (fun u _ => mul_nonneg (hpownn _ _ _) (hnn u z))
        ⟨y, Finset.mem_univ y, ?_⟩
      exact mul_pos (ih σ τ) (glauber_pos π hpos y z v hzy)
  intro σ τ
  refine ⟨(Finset.univ : Finset Vv).card, ?_⟩
  have h := hkey Finset.univ σ τ
  have he : (fun w => if w ∈ (Finset.univ : Finset Vv) then τ w else σ w) = τ := by
    funext w; simp
  rwa [he] at h

end Irr

/-! ### The edge-measure comparison and the spectral gap -/

section Main

variable [Nonempty Vv] {G G' : SimpleGraph Vv} [DecidableRel G.Adj] [DecidableRel G'.Adj]

lemma degree_mono (hsub : G' ≤ G) (v : Vv) : G'.degree v ≤ G.degree v := by
  refine Finset.card_le_card fun w hw => ?_
  rw [SimpleGraph.mem_neighborFinset] at hw ⊢
  exact hsub hw

lemma locfield_le_max (σ : Vv → Bool) (v : Vv) : |locfield G σ v| ≤ (G.maxDegree : ℝ) := by
  refine le_trans (locfield_abs_le σ v) ?_
  exact_mod_cast G.degree_le_maxDegree v

lemma locfield_le_max' (hsub : G' ≤ G) (σ : Vv → Bool) (v : Vv) :
    |locfield G' σ v| ≤ (G.maxDegree : ℝ) := by
  refine le_trans (locfield_abs_le σ v) ?_
  exact_mod_cast le_trans (degree_mono hsub v) (G.degree_le_maxDegree v)

lemma normalizer_eq (π : (Vv → Bool) → ℝ) (σ τ : Vv → Bool) (v : Vv)
    (h : ∀ w : Vv, w ≠ v → τ w = σ w) :
    (∑ z ∈ Finset.univ.filter (fun z : Vv → Bool => ∀ w : Vv, w ≠ v → z w = σ w), π z)
      = π τ + π (flipAt τ v) := by
  have hset : (Finset.univ.filter (fun z : Vv → Bool => ∀ w : Vv, w ≠ v → z w = σ w))
      = (Finset.univ.filter (fun z : Vv → Bool => ∀ w : Vv, w ≠ v → z w = τ w)) := by
    refine Finset.filter_congr fun z _ => ?_
    constructor
    · intro hz w hw
      rw [hz w hw, ← h w hw]
    · intro hz w hw
      rw [hz w hw, h w hw]
  rw [hset, agree_set τ v, Finset.sum_pair (flipAt_ne τ v)]

lemma glauber_edge (π : (Vv → Bool) → ℝ) (σ τ : Vv → Bool) :
    π σ * glauber π σ τ
      = (Fintype.card Vv : ℝ)⁻¹ * ∑ v : Vv,
          (if ∀ w : Vv, w ≠ v → τ w = σ w then π σ * pcond π τ v else 0) := by
  show π σ * ((Fintype.card Vv : ℝ)⁻¹ * ∑ v : Vv, _) = _
  rw [← mul_assoc, mul_comm (π σ), mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : ∀ w : Vv, w ≠ v → τ w = σ w
  · rw [if_pos hv, if_pos hv, normalizer_eq π σ τ v hv]
    rfl
  · rw [if_neg hv, if_neg hv, mul_zero]

lemma edge_compare (hsub : G' ≤ G) {β : ℝ} (hβ : 0 ≤ β) (σ τ : Vv → Bool) :
    isingDist G' β σ * glauber (isingDist G' β) σ τ
      ≤ (Real.exp (2 * (β * rr G G')) * Real.exp (2 * β * (G.maxDegree : ℝ))) *
        (isingDist G β σ * glauber (isingDist G β) σ τ) := by
  rw [glauber_edge (isingDist G' β) σ τ, glauber_edge (isingDist G β) σ τ]
  set E : ℝ := Real.exp (2 * (β * rr G G')) * Real.exp (2 * β * (G.maxDegree : ℝ)) with hE
  have hc : (0:ℝ) ≤ (Fintype.card Vv : ℝ)⁻¹ := by positivity
  have hΔ : (0:ℝ) ≤ (G.maxDegree : ℝ) := by positivity
  have hsum : (∑ v : Vv, (if ∀ w : Vv, w ≠ v → τ w = σ w then
        isingDist G' β σ * pcond (isingDist G' β) τ v else 0))
      ≤ E * ∑ v : Vv, (if ∀ w : Vv, w ≠ v → τ w = σ w then
        isingDist G β σ * pcond (isingDist G β) τ v else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases hv : ∀ w : Vv, w ≠ v → τ w = σ w
    · rw [if_pos hv, if_pos hv]
      have h1 := (dist_ratio hsub hβ σ).2
      have h2 := pcond_ratio (G := G) (G' := G') hβ hΔ τ v
        (locfield_le_max τ v) (locfield_le_max' hsub τ v)
      calc isingDist G' β σ * pcond (isingDist G' β) τ v
          ≤ (Real.exp (2 * (β * rr G G')) * isingDist G β σ) *
              (Real.exp (2 * β * (G.maxDegree : ℝ)) * pcond (isingDist G β) τ v) :=
            mul_le_mul h1 h2 (pcond_pos G' β τ v).le
              (mul_nonneg (Real.exp_pos _).le (isingDist_pos G β σ).le)
        _ = E * (isingDist G β σ * pcond (isingDist G β) τ v) := by rw [hE]; ring
    · rw [if_neg hv, if_neg hv, mul_zero]
  calc (Fintype.card Vv : ℝ)⁻¹ * ∑ v : Vv, (if ∀ w : Vv, w ≠ v → τ w = σ w then
        isingDist G' β σ * pcond (isingDist G' β) τ v else 0)
      ≤ (Fintype.card Vv : ℝ)⁻¹ * (E * ∑ v : Vv, (if ∀ w : Vv, w ≠ v → τ w = σ w then
        isingDist G β σ * pcond (isingDist G β) τ v else 0)) :=
        mul_le_mul_of_nonneg_left hsum hc
    _ = E * ((Fintype.card Vv : ℝ)⁻¹ * ∑ v : Vv, (if ∀ w : Vv, w ≠ v → τ w = σ w then
        isingDist G β σ * pcond (isingDist G β) τ v else 0)) := by ring

end Main

end Ising

open Ising

theorem solution {Vv : Type*} [Fintype Vv] [DecidableEq Vv]
    [Nonempty Vv] (G G' : SimpleGraph Vv) [DecidableRel G.Adj]
    [DecidableRel G'.Adj] (hsub : G' ≤ G) (β : ℝ) (hβ : 0 < β) :
    MarkovMixing.spectralGap (MarkovMixing.glauber (MarkovMixing.isingDist G' β)) ≤
      Real.exp (2 * β * ((G.maxDegree : ℝ) +
        2 * ((G.edgeFinset \ G'.edgeFinset).card : ℝ))) *
      MarkovMixing.spectralGap (MarkovMixing.glauber (MarkovMixing.isingDist G β)) := by
  classical
  have hβ0 : (0:ℝ) ≤ β := hβ.le
  have hd : IsDist (isingDist G β) := isingDist_isDist G β
  have hd' : IsDist (isingDist G' β) := isingDist_isDist G' β
  have hp : ∀ σ, 0 < isingDist G β σ := isingDist_pos G β
  have hp' : ∀ σ, 0 < isingDist G' β σ := isingDist_pos G' β
  set P : Matrix (Vv → Bool) (Vv → Bool) ℝ := glauber (isingDist G β) with hPdef
  set P' : Matrix (Vv → Bool) (Vv → Bool) ℝ := glauber (isingDist G' β) with hP'def
  have hgs := MarkovMixing.glauber_stationary (isingDist G β) hd
  have hgs' := MarkovMixing.glauber_stationary (isingDist G' β) hd'
  have hPst : MarkovMixing.IsStochastic P := ⟨hgs.1, fun x => hgs.2.1 x (hp x)⟩
  have hPst' : MarkovMixing.IsStochastic P' := ⟨hgs'.1, fun x => hgs'.2.1 x (hp' x)⟩
  have hirr : MarkovMixing.Irreducible P := glauber_irreducible _ hd hp
  have hirr' : MarkovMixing.Irreducible P' := glauber_irreducible _ hd' hp'
  have hcard2 : 2 ≤ Fintype.card (Vv → Bool) := by
    rw [Fintype.card_fun]
    have h1 : 1 ≤ Fintype.card Vv := Fintype.card_pos
    calc 2 = Fintype.card Bool ^ 1 := by simp
      _ ≤ Fintype.card Bool ^ Fintype.card Vv := Nat.pow_le_pow_right (by simp) h1
  set B : ℝ := Real.exp (2 * (β * rr G G')) * Real.exp (2 * β * (G.maxDegree : ℝ)) with hB
  have hBpos : (0:ℝ) < B := by rw [hB]; positivity
  -- the Dirichlet forms compare edge by edge
  have hcomp : ∀ f : (Vv → Bool) → ℝ,
      dirichletForm P' (isingDist G' β) f ≤ B * dirichletForm P (isingDist G β) f := by
    intro f
    have hterm : ∀ x y : Vv → Bool,
        (f x - f y) ^ 2 * (isingDist G' β x * P' x y)
          ≤ B * ((f x - f y) ^ 2 * (isingDist G β x * P x y)) := by
      intro x y
      have h := edge_compare hsub hβ0 x y
      have hsq : (0:ℝ) ≤ (f x - f y) ^ 2 := sq_nonneg _
      nlinarith [h, hsq]
    have hpull : ∑ x : Vv → Bool, ∑ y : Vv → Bool,
          B * ((f x - f y) ^ 2 * (isingDist G β x * P x y))
        = B * ∑ x : Vv → Bool, ∑ y : Vv → Bool,
          (f x - f y) ^ 2 * (isingDist G β x * P x y) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
    show 2⁻¹ * ∑ x : Vv → Bool, ∑ y : Vv → Bool,
        (f x - f y) ^ 2 * (isingDist G' β x * P' x y)
      ≤ B * (2⁻¹ * ∑ x : Vv → Bool, ∑ y : Vv → Bool,
        (f x - f y) ^ 2 * (isingDist G β x * P x y))
    calc 2⁻¹ * ∑ x : Vv → Bool, ∑ y : Vv → Bool,
          (f x - f y) ^ 2 * (isingDist G' β x * P' x y)
        ≤ 2⁻¹ * ∑ x : Vv → Bool, ∑ y : Vv → Bool,
          B * ((f x - f y) ^ 2 * (isingDist G β x * P x y)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
      _ = B * (2⁻¹ * ∑ x : Vv → Bool, ∑ y : Vv → Bool,
          (f x - f y) ^ 2 * (isingDist G β x * P x y)) := by rw [hpull]; ring
  have hres := MarkovMixing.dirichlet_comparison_irreducible hcard2 P P' hPst hPst' hirr hirr'
    (isingDist G β) (isingDist G' β) hgs.2.2.2 hgs'.2.2.2 hgs.2.2.1 hgs'.2.2.1 hp' B hBpos hcomp
  -- the density ratio is at most `e^{2βr}`
  have hsup : (⨆ x : Vv → Bool, isingDist G β x / isingDist G' β x)
      ≤ Real.exp (2 * (β * rr G G')) := by
    refine ciSup_le fun σ => ?_
    rw [div_le_iff₀ (hp' σ)]
    exact (dist_ratio hsub hβ0 σ).1
  -- the gap on the right is nonnegative
  have hgap : 0 ≤ MarkovMixing.spectralGap P := by
    have hle : MarkovMixing.lambdaTwo P ≤ 1 := by
      refine Real.sSup_le (fun x hx => ?_) zero_le_one
      exact (abs_le.mp ((MarkovMixing.eigenvalue_basic P hPst).1 x hx.1)).2
    show 0 ≤ 1 - MarkovMixing.lambdaTwo P
    linarith
  have hexp : Real.exp (2 * (β * rr G G')) * B
      = Real.exp (2 * β * ((G.maxDegree : ℝ) + 2 * rr G G')) := by
    rw [hB, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  refine le_trans hres ?_
  have hstep : (⨆ x : Vv → Bool, isingDist G β x / isingDist G' β x) * B
      ≤ Real.exp (2 * β * ((G.maxDegree : ℝ) + 2 * rr G G')) := by
    rw [← hexp]
    exact mul_le_mul_of_nonneg_right hsup hBpos.le
  exact mul_le_mul_of_nonneg_right hstep hgap
