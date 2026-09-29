-- Prove2me | solution 2 for MarkovMixing.ising_block_dynamics
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-23T04:00:49.914111+00:00
-- url     : https://prove2.me/submissions/2a4ff446-5aa3-4dda-975e-a9bd376c3c61

import Definitions.Def_mm_ising
import Theorems.Thm_MarkovMixing_dirichlet_gap
import Theorems.Thm_MarkovMixing_glauber_stationary
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Chebyshev

/-!
# Comparison of block dynamics and single-site Glauber dynamics (LPW Theorem 15.9)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset

section Blocks

variable {Vv : Type*} [Fintype Vv] [DecidableEq Vv]
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The cylinder of configurations agreeing with `σ` off `W`. -/
private def cyl (W : Finset Vv) (σ : Vv → S) : Finset (Vv → S) :=
  univ.filter fun η : Vv → S => ∀ w ∉ W, η w = σ w

private lemma sum_div_const {α : Type*} (s : Finset α) (f : α → ℝ) (c : ℝ) :
    (∑ i ∈ s, f i) / c = ∑ i ∈ s, f i / c := by
  simp [div_eq_mul_inv, Finset.sum_mul]

private lemma mem_cyl (W : Finset Vv) (σ η : Vv → S) :
    η ∈ cyl W σ ↔ ∀ w ∉ W, η w = σ w := by simp [cyl]

private lemma cyl_self (W : Finset Vv) (σ : Vv → S) : σ ∈ cyl W σ := by
  rw [mem_cyl]
  intro w _
  rfl

private lemma cyl_eq (W : Finset Vv) (σ τ : Vv → S) (h : τ ∈ cyl W σ) :
    cyl W τ = cyl W σ := by
  rw [mem_cyl] at h
  ext η
  rw [mem_cyl, mem_cyl]
  constructor
  · intro hh w hw
    rw [hh w hw, h w hw]
  · intro hh w hw
    rw [hh w hw, h w hw]

private lemma blockUpdate_apply (π : (Vv → S) → ℝ) (W : Finset Vv) (σ τ : Vv → S) :
    blockUpdate π W σ τ = if τ ∈ cyl W σ then π τ / ∑ η ∈ cyl W σ, π η else 0 := by
  simp only [blockUpdate]
  by_cases h : ∀ w ∉ W, τ w = σ w
  · rw [if_pos h, if_pos ((mem_cyl W σ τ).mpr h)]
    rfl
  · rw [if_neg h, if_neg (fun hc => h ((mem_cyl W σ τ).mp hc))]

private lemma cyl_sum_pos (π : (Vv → S) → ℝ) (hpos : ∀ x, 0 < π x) (W : Finset Vv)
    (σ : Vv → S) : 0 < ∑ η ∈ cyl W σ, π η :=
  Finset.sum_pos (fun η _ => hpos η) ⟨σ, cyl_self W σ⟩

private lemma blockUpdate_stochastic (π : (Vv → S) → ℝ) (hpos : ∀ x, 0 < π x)
    (W : Finset Vv) : IsStochastic (blockUpdate π W) := by
  refine ⟨fun σ τ => ?_, fun σ => ?_⟩
  · rw [blockUpdate_apply]
    split_ifs
    · exact le_of_lt (div_pos (hpos τ) (cyl_sum_pos π hpos W σ))
    · exact le_refl 0
  · rw [Finset.sum_congr rfl fun τ _ => blockUpdate_apply π W σ τ,
      ← Finset.sum_filter]
    have hfil : (univ.filter fun τ : Vv → S => τ ∈ cyl W σ) = cyl W σ := by
      ext τ; simp
    rw [hfil, ← sum_div_const, div_self (ne_of_gt (cyl_sum_pos π hpos W σ))]

private lemma blockUpdate_reversible (π : (Vv → S) → ℝ) (hpos : ∀ x, 0 < π x)
    (W : Finset Vv) : DetailedBalance (blockUpdate π W) π := by
  intro σ τ
  rw [blockUpdate_apply, blockUpdate_apply]
  by_cases h : τ ∈ cyl W σ
  · have h' : σ ∈ cyl W τ := by
      rw [mem_cyl] at h ⊢
      intro w hw
      exact (h w hw).symm
    rw [if_pos h, if_pos h', cyl_eq W σ τ h]
    field_simp
    try ring
  · have h' : σ ∉ cyl W τ := by
      intro hc
      refine h ?_
      rw [mem_cyl] at hc ⊢
      intro w hw
      exact (hc w hw).symm
    rw [if_neg h, if_neg h']
    ring

private lemma blockDynamics_stochastic (π : (Vv → S) → ℝ) (hpos : ∀ x, 0 < π x)
    {b : ℕ} (hb : 0 < b) (blocks : Fin b → Finset Vv) :
    IsStochastic (blockDynamics π blocks) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  refine ⟨fun σ τ => ?_, fun σ => ?_⟩
  · rw [blockDynamics]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
    exact (blockUpdate_stochastic π hpos (blocks i)).1 σ τ
  · simp only [blockDynamics]
    rw [← Finset.mul_sum, Finset.sum_comm]
    rw [Finset.sum_congr rfl fun i _ => (blockUpdate_stochastic π hpos (blocks i)).2 σ]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp

private lemma blockDynamics_reversible (π : (Vv → S) → ℝ) (hpos : ∀ x, 0 < π x)
    {b : ℕ} (blocks : Fin b → Finset Vv) :
    DetailedBalance (blockDynamics π blocks) π := by
  intro σ τ
  simp only [blockDynamics]
  rw [show π σ * ((b : ℝ)⁻¹ * ∑ i, blockUpdate π (blocks i) σ τ)
      = (b : ℝ)⁻¹ * ∑ i, π σ * blockUpdate π (blocks i) σ τ from by
        rw [← Finset.mul_sum]; ring,
    show π τ * ((b : ℝ)⁻¹ * ∑ i, blockUpdate π (blocks i) τ σ)
      = (b : ℝ)⁻¹ * ∑ i, π τ * blockUpdate π (blocks i) τ σ from by
        rw [← Finset.mul_sum]; ring]
  congr 1
  exact Finset.sum_congr rfl fun i _ => blockUpdate_reversible π hpos (blocks i) σ τ

private lemma stationary_of_reversible (P : Matrix (Vv → S) (Vv → S) ℝ)
    (hP : IsStochastic P) (π : (Vv → S) → ℝ) (hπ : IsDist π)
    (hrev : DetailedBalance P π) : IsStationary P π := by
  refine ⟨hπ, ?_⟩
  ext τ
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_congr rfl fun σ _ => hrev σ τ, ← Finset.mul_sum, hP.2 τ, mul_one]

/-! ### Canonical paths inside a block -/

variable [Nonempty Vv]

/-- The position of `v` in a fixed enumeration of the block `W`. -/
private def ixf (W : Finset Vv) (v : Vv) : ℕ :=
  if h : v ∈ W then ((W.equivFin ⟨v, h⟩ : Fin W.card) : ℕ) else 0

/-- The `k`-th site of `W` in that enumeration. -/
private def ste (W : Finset Vv) (k : ℕ) : Vv :=
  if h : k < W.card then ((W.equivFin.symm ⟨k, h⟩ : {x // x ∈ W}) : Vv)
  else Classical.arbitrary Vv

private lemma ste_mem (W : Finset Vv) {k : ℕ} (hk : k < W.card) : ste W k ∈ W := by
  rw [ste, dif_pos hk]
  exact (W.equivFin.symm ⟨k, hk⟩).2

private lemma ixf_lt (W : Finset Vv) {v : Vv} (hv : v ∈ W) : ixf W v < W.card := by
  rw [ixf, dif_pos hv]
  exact (W.equivFin ⟨v, hv⟩).2

private lemma ixf_ste (W : Finset Vv) {k : ℕ} (hk : k < W.card) : ixf W (ste W k) = k := by
  have hm := ste_mem W hk
  rw [ixf, dif_pos hm]
  have hsub : W.equivFin.symm ⟨k, hk⟩ = (⟨ste W k, hm⟩ : {x // x ∈ W}) := by
    apply Subtype.ext
    show ((W.equivFin.symm ⟨k, hk⟩ : {x // x ∈ W}) : Vv) = ste W k
    rw [ste, dif_pos hk]
  rw [← hsub, Equiv.apply_symm_apply]

private lemma ste_ixf (W : Finset Vv) {v : Vv} (hv : v ∈ W) : ste W (ixf W v) = v := by
  have hk := ixf_lt W hv
  rw [ste, dif_pos hk]
  have hfin : W.equivFin ⟨v, hv⟩ = (⟨ixf W v, hk⟩ : Fin W.card) := by
    apply Fin.ext
    show ((W.equivFin ⟨v, hv⟩ : Fin W.card) : ℕ) = ixf W v
    rw [ixf, dif_pos hv]
  rw [← hfin, Equiv.symm_apply_apply]

/-- Summing over the enumeration of a block is summing over the block. -/
private lemma sum_range_ste (W : Finset Vv) (X : Vv → ℝ) :
    ∑ k ∈ Finset.range W.card, X (ste W k) = ∑ v ∈ W, X v := by
  refine Finset.sum_nbij' (fun k => ste W k) (fun v => ixf W v) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    exact ste_mem W (Finset.mem_range.mp hk)
  · intro v hv
    exact Finset.mem_range.mpr (ixf_lt W hv)
  · intro k hk
    exact ixf_ste W (Finset.mem_range.mp hk)
  · intro v hv
    exact ste_ixf W hv
  · intro k _
    rfl

/-- The `k`-th configuration on the canonical path from `σ` to `τ` inside `W`. -/
private def mixc (W : Finset Vv) (σ τ : Vv → S) (k : ℕ) : Vv → S :=
  fun v => if v ∈ W ∧ ixf W v < k then τ v else σ v

private lemma mixc_zero (W : Finset Vv) (σ τ : Vv → S) : mixc W σ τ 0 = σ := by
  funext v
  rw [mixc, if_neg]
  rintro ⟨-, h⟩
  exact absurd h (Nat.not_lt_zero _)

private lemma mixc_card (W : Finset Vv) (σ τ : Vv → S) (h : τ ∈ cyl W σ) :
    mixc W σ τ W.card = τ := by
  rw [mem_cyl] at h
  funext v
  rw [mixc]
  by_cases hv : v ∈ W
  · rw [if_pos ⟨hv, ixf_lt W hv⟩]
  · rw [if_neg (fun hc => hv hc.1), h v hv]

private lemma mixc_off (W : Finset Vv) (σ τ : Vv → S) (k : ℕ) {v : Vv} (hv : v ∉ W) :
    mixc W σ τ k v = σ v := by
  rw [mixc, if_neg (fun hc => hv hc.1)]

private lemma mixc_succ (W : Finset Vv) (σ τ : Vv → S) {k : ℕ} (hk : k < W.card) :
    mixc W σ τ (k + 1) = Function.update (mixc W σ τ k) (ste W k) (τ (ste W k)) := by
  funext v
  rw [Function.update_apply]
  by_cases hv : v = ste W k
  · subst hv
    rw [if_pos rfl, mixc, if_pos ⟨ste_mem W hk, by rw [ixf_ste W hk]; omega⟩]
  · rw [if_neg hv, mixc, mixc]
    by_cases hw : v ∈ W
    · by_cases hlt : ixf W v < k
      · rw [if_pos ⟨hw, by omega⟩, if_pos ⟨hw, hlt⟩]
      · have hne : ixf W v ≠ k := by
          intro hc
          exact hv (by rw [← hc, ste_ixf W hw])
        rw [if_neg (fun hc => by omega), if_neg (fun hc => hlt hc.2)]
    · rw [if_neg (fun hc => hw hc.1), if_neg (fun hc => hw hc.1)]

/-- The exchange map on pairs used to reindex the canonical-path sums. -/
private def swp (W : Finset Vv) (k : ℕ) :
    ((Vv → S) × (Vv → S)) → ((Vv → S) × (Vv → S)) :=
  fun p => (mixc W p.1 p.2 k, mixc W p.2 p.1 k)

private lemma swp_invol (W : Finset Vv) (k : ℕ) :
    Function.Involutive (swp (S := S) W k) := by
  intro p
  obtain ⟨σ, τ⟩ := p
  have h1 : mixc W (mixc W σ τ k) (mixc W τ σ k) k = σ := by
    funext v
    simp only [mixc]
    by_cases hc : v ∈ W ∧ ixf W v < k
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
  have h2 : mixc W (mixc W τ σ k) (mixc W σ τ k) k = τ := by
    funext v
    simp only [mixc]
    by_cases hc : v ∈ W ∧ ixf W v < k
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
  simp only [swp]
  rw [h1, h2]

private lemma mixc_mem_cyl (W : Finset Vv) (σ τ : Vv → S) (k : ℕ) (h : τ ∈ cyl W σ) :
    mixc W τ σ k ∈ cyl W (mixc W σ τ k) := by
  rw [mem_cyl] at h ⊢
  intro w hw
  rw [mixc_off W τ σ k hw, mixc_off W σ τ k hw]
  exact h w hw

/-- Cylinders over a block are small. -/
private lemma card_cyl_le (W : Finset Vv) (σ : Vv → S) :
    (cyl W σ).card ≤ Fintype.card S ^ W.card := by
  classical
  have hinj : Set.InjOn (fun η : Vv → S => fun w : {x // x ∈ W} => η w.1)
      (cyl W σ : Set (Vv → S)) := by
    intro a ha b hb hab
    have ha' := (mem_cyl W σ a).mp (by simpa using ha)
    have hb' := (mem_cyl W σ b).mp (by simpa using hb)
    funext v
    by_cases hv : v ∈ W
    · exact congrFun hab ⟨v, hv⟩
    · rw [ha' v hv, hb' v hv]
  have := Finset.card_le_card_of_injOn
    (f := fun η : Vv → S => fun w : {x // x ∈ W} => η w.1)
    (t := (Finset.univ : Finset ({x // x ∈ W} → S)))
    (fun a _ => Finset.mem_univ _) hinj
  calc (cyl W σ).card ≤ (Finset.univ : Finset ({x // x ∈ W} → S)).card := this
    _ = Fintype.card S ^ W.card := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe]

/-! ### Glauber dynamics as block dynamics over singletons -/

private lemma glauber_eq_blocks (π : (Vv → S) → ℝ) (σ τ : Vv → S) :
    glauber π σ τ
      = (Fintype.card Vv : ℝ)⁻¹ * ∑ v : Vv, blockUpdate π ({v} : Finset Vv) σ τ := by
  rw [glauber]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  have hset : (Finset.univ.filter (fun z : Vv → S => ∀ w : Vv, w ≠ v → z w = σ w))
      = Finset.univ.filter (fun z : Vv → S => ∀ w ∉ ({v} : Finset Vv), z w = σ w) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [blockUpdate]
  by_cases h : ∀ w : Vv, w ≠ v → τ w = σ w
  · rw [if_pos h, if_pos (by simpa using h), hset]
  · rw [if_neg h, if_neg (by simpa using h)]


private lemma blockUpdate_le_one (π : (Vv → S) → ℝ) (hpos : ∀ x, 0 < π x) (W : Finset Vv)
    (σ τ : Vv → S) : blockUpdate π W σ τ ≤ 1 := by
  rw [blockUpdate_apply]
  split_ifs with h
  · rw [div_le_one (cyl_sum_pos π hpos W σ)]
    exact Finset.single_le_sum (f := π) (fun ξ _ => (hpos ξ).le) h
  · norm_num

private lemma mixc_cyl_iff (W : Finset Vv) (η ζ : Vv → S) (k : ℕ) :
    mixc W ζ η k ∈ cyl W (mixc W η ζ k) ↔ ζ ∈ cyl W η := by
  rw [mem_cyl, mem_cyl]
  constructor
  · intro h w hw
    have hh := h w hw
    rwa [mixc_off W ζ η k hw, mixc_off W η ζ k hw] at hh
  · intro h w hw
    rw [mixc_off W ζ η k hw, mixc_off W η ζ k hw]
    exact h w hw

private lemma cyl_singleton_eq (η : Vv → S) (v : Vv) :
    cyl ({v} : Finset Vv) η
      = Finset.image (fun s : S => Function.update η v s) Finset.univ := by
  ext ξ
  rw [mem_cyl, Finset.mem_image]
  constructor
  · intro h
    refine ⟨ξ v, Finset.mem_univ _, ?_⟩
    funext u
    rw [Function.update_apply]
    by_cases hu : u = v
    · rw [if_pos hu, hu]
    · rw [if_neg hu]
      exact (h u (by simpa using hu)).symm
  · rintro ⟨s, -, rfl⟩ w hw
    rw [Function.update_apply, if_neg (by simpa using hw)]

private lemma update_inj (η : Vv → S) (v : Vv) :
    ∀ s ∈ (Finset.univ : Finset S), ∀ s' ∈ (Finset.univ : Finset S),
      Function.update η v s = Function.update η v s' → s = s' := by
  intro s _ s' _ h
  have := congrFun h v
  rwa [Function.update_apply, Function.update_apply, if_pos rfl, if_pos rfl] at this

private lemma sum_bool_update_le (η : Vv → S) (v : Vv) (F : (Vv → S) → ℝ)
    (hF : ∀ ρ, 0 ≤ F ρ) :
    ∑ s : S, F (Function.update η v s) ≤ ∑ ρ : Vv → S, F ρ := by
  rw [← Finset.sum_image (update_inj η v)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun ρ _ _ => hF ρ)

private lemma sum_cyl_fiber (W : Finset Vv) (η : Vv → S) (v : Vv) (g : S → ℝ)
    (hg : ∀ s, 0 ≤ g s) :
    ∑ ζ ∈ cyl W η, g (ζ v) ≤ ((cyl W η).card : ℝ) * ∑ s : S, g s := by
  classical
  have h1 : ∑ s : S, ∑ ζ ∈ (cyl W η).filter (fun ζ => ζ v = s), g (ζ v)
      = ∑ ζ ∈ cyl W η, g (ζ v) :=
    Finset.sum_fiberwise_of_maps_to (fun ζ _ => Finset.mem_univ (ζ v)) _
  rw [← h1, Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  have h2 : ∑ ζ ∈ (cyl W η).filter (fun ζ => ζ v = s), g (ζ v)
      = ((((cyl W η).filter (fun ζ => ζ v = s)).card : ℕ) : ℝ) * g s := by
    rw [Finset.sum_congr rfl (fun ζ hζ => by rw [(Finset.mem_filter.mp hζ).2]),
      Finset.sum_const, nsmul_eq_mul]
  rw [h2]
  refine mul_le_mul_of_nonneg_right ?_ (hg s)
  exact_mod_cast Finset.card_filter_le _ _

private lemma mixc_patch (W : Finset Vv) (η ζ : Vv → S) (k : ℕ) :
    mixc W η ζ k = fun u => if u ∈ W.filter (fun u => ixf W u < k) then ζ u else η u := by
  funext u
  rw [mixc]
  by_cases h : u ∈ W ∧ ixf W u < k
  · rw [if_pos h, if_pos (Finset.mem_filter.mpr h)]
  · rw [if_neg h, if_neg (fun hc => h (Finset.mem_filter.mp hc))]

private lemma mixc_patch2 (W : Finset Vv) (η ζ : Vv → S) {k : ℕ} (hk : k < W.card) :
    mixc W η ζ k
      = fun u => if u ∈ insert (ste W k) (W.filter (fun u => ixf W u < k))
                 then (Function.update ζ (ste W k) (η (ste W k))) u
                 else (Function.update η (ste W k) (ζ (ste W k))) u := by
  funext u
  have hixv : ixf W (ste W k) = k := ixf_ste W hk
  by_cases hu : u = ste W k
  · subst hu
    rw [mixc, if_neg (by rw [hixv]; exact fun hc => absurd hc.2 (Nat.lt_irrefl k)),
      if_pos (Finset.mem_insert_self _ _), Function.update_apply, if_pos rfl]
  · rw [mixc]
    by_cases hf : u ∈ W.filter (fun u => ixf W u < k)
    · rw [if_pos (Finset.mem_filter.mp hf), if_pos (Finset.mem_insert_of_mem hf),
        Function.update_apply, if_neg hu]
    · rw [if_neg (fun hc => hf (Finset.mem_filter.mpr hc)),
        if_neg (fun hc => by
          rcases Finset.mem_insert.mp hc with h | h
          · exact hu h
          · exact hf h),
        Function.update_apply, if_neg hu]

private lemma min_le_two_mul (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    min a c ≤ 2 * (a * (c / (a + c))) := by
  have hac : (0:ℝ) < a + c := by linarith
  have key : 2 * (a * (c / (a + c))) = 2*a*c/(a+c) := by field_simp; try ring
  rw [key]
  rcases le_total a c with h | h
  · rw [min_eq_left h, le_div_iff₀ hac]; nlinarith
  · rw [min_eq_right h, le_div_iff₀ hac]; nlinarith


/-! ### Irreducibility -/

private lemma pow_nonneg_of_stochastic {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (hP : IsStochastic P) : ∀ (n : ℕ) (x y : X), 0 ≤ (P ^ n) x y := by
  intro n
  induction n with
  | zero =>
      intro x y
      rw [pow_zero, Matrix.one_apply]
      split_ifs <;> norm_num
  | succ n ih =>
      intro x y
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP.1 z y)

private lemma pow_pos_step {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (hP : IsStochastic P) {n : ℕ} {σ ρ τ : X}
    (h1 : 0 < (P ^ n) σ ρ) (h2 : 0 < P ρ τ) : 0 < (P ^ (n + 1)) σ τ := by
  rw [pow_succ, Matrix.mul_apply]
  refine lt_of_lt_of_le (mul_pos h1 h2) ?_
  exact Finset.single_le_sum (f := fun z => (P ^ n) σ z * P z τ)
    (fun z _ => mul_nonneg (pow_nonneg_of_stochastic P hP n σ z) (hP.1 z τ))
    (Finset.mem_univ ρ)

private lemma blockUpdate_pos (π : (Vv → S) → ℝ) (hpos : ∀ x, 0 < π x) (W : Finset Vv)
    (σ τ : Vv → S) (h : τ ∈ cyl W σ) : 0 < blockUpdate π W σ τ := by
  rw [blockUpdate_apply, if_pos h]
  exact div_pos (hpos τ) (cyl_sum_pos π hpos W σ)

private lemma glauber_stoch' [Nonempty Vv] (π : (Vv → S) → ℝ) (hpos : ∀ x, 0 < π x) :
    IsStochastic (glauber π) := by
  have hN : (0 : ℝ) < (Fintype.card Vv : ℝ) := by exact_mod_cast Fintype.card_pos
  constructor
  · intro σ τ
    rw [glauber_eq_blocks]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun v _ => (blockUpdate_stochastic π hpos _).1 σ τ)
  · intro σ
    rw [Finset.sum_congr rfl fun τ _ => glauber_eq_blocks π σ τ, ← Finset.mul_sum,
      Finset.sum_comm]
    rw [Finset.sum_congr rfl fun v _ => (blockUpdate_stochastic π hpos _).2 σ]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    field_simp

private lemma glauber_pos [Nonempty Vv] (π : (Vv → S) → ℝ) (hpos : ∀ x, 0 < π x)
    (v : Vv) (σ τ : Vv → S) (h : τ ∈ cyl ({v} : Finset Vv) σ) : 0 < glauber π σ τ := by
  have hN : (0 : ℝ) < (Fintype.card Vv : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [glauber_eq_blocks]
  refine mul_pos (by positivity) ?_
  exact Finset.sum_pos' (fun w _ => (blockUpdate_stochastic π hpos _).1 σ τ)
    ⟨v, Finset.mem_univ v, blockUpdate_pos π hpos _ σ τ h⟩

private lemma blockDynamics_pos (π : (Vv → S) → ℝ) (hpos : ∀ x, 0 < π x)
    {b : ℕ} (hb : 0 < b) (blocks : Fin b → Finset Vv) (i : Fin b)
    (σ τ : Vv → S) (h : τ ∈ cyl (blocks i) σ) : 0 < blockDynamics π blocks σ τ := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [blockDynamics]
  refine mul_pos (by positivity) ?_
  exact Finset.sum_pos' (fun j _ => (blockUpdate_stochastic π hpos _).1 σ τ)
    ⟨i, Finset.mem_univ i, blockUpdate_pos π hpos _ σ τ h⟩

private lemma glauber_irred [Nonempty Vv] (π : (Vv → S) → ℝ) (hpos : ∀ x, 0 < π x) :
    Irreducible (glauber π) := by
  intro σ τ
  have hst := glauber_stoch' π hpos
  have key : ∀ j : ℕ, j ≤ (Finset.univ : Finset Vv).card →
      0 < ((glauber π) ^ j) σ (mixc Finset.univ σ τ j) := by
    intro j
    induction j with
    | zero =>
        intro _
        rw [pow_zero, mixc_zero, Matrix.one_apply_eq]
        norm_num
    | succ j ih =>
        intro hj
        have hjlt : j < (Finset.univ : Finset Vv).card := by omega
        have h1 := ih (by omega)
        have h2 : 0 < glauber π (mixc Finset.univ σ τ j) (mixc Finset.univ σ τ (j + 1)) := by
          refine glauber_pos π hpos (ste Finset.univ j) _ _ ?_
          rw [mixc_succ Finset.univ σ τ hjlt, mem_cyl]
          intro w hw
          rw [Function.update_apply, if_neg (by simpa using hw)]
        exact pow_pos_step (glauber π) hst h1 h2
  have hfin := key (Finset.univ : Finset Vv).card (le_refl _)
  rw [mixc_card Finset.univ σ τ
    (by rw [mem_cyl]; intro w hw; exact absurd (Finset.mem_univ w) hw)] at hfin
  exact ⟨_, hfin⟩

private def upto {b : ℕ} (blocks : Fin b → Finset Vv) (j : ℕ) : Finset Vv :=
  ((Finset.univ : Finset (Fin b)).filter fun i => i.val < j).biUnion blocks

private lemma mem_upto {b : ℕ} (blocks : Fin b → Finset Vv) (j : ℕ) (v : Vv) :
    v ∈ upto blocks j ↔ ∃ i : Fin b, i.val < j ∧ v ∈ blocks i := by
  simp [upto, Finset.mem_biUnion, Finset.mem_filter]

private def zetaC {b : ℕ} (blocks : Fin b → Finset Vv) (σ τ : Vv → S) (j : ℕ) (v : Vv) : S :=
  if v ∈ upto blocks j then τ v else σ v

private lemma blockDynamics_irred [Nonempty Vv] (π : (Vv → S) → ℝ) (hpos : ∀ x, 0 < π x)
    {b : ℕ} (hb : 0 < b) (blocks : Fin b → Finset Vv)
    (hcover : ∀ v : Vv, ∃ i : Fin b, v ∈ blocks i) :
    Irreducible (blockDynamics π blocks) := by
  intro σ τ
  have hst := blockDynamics_stochastic π hpos hb blocks
  have hz0 : zetaC blocks σ τ 0 = σ := by
    funext v
    rw [zetaC, if_neg]
    rw [mem_upto]
    rintro ⟨i, hi, -⟩
    omega
  have hzb : zetaC blocks σ τ b = τ := by
    funext v
    obtain ⟨i, hi⟩ := hcover v
    rw [zetaC, if_pos]
    rw [mem_upto]
    exact ⟨i, i.isLt, hi⟩
  have key : ∀ j : ℕ, j ≤ b →
      0 < ((blockDynamics π blocks) ^ j) σ (zetaC blocks σ τ j) := by
    intro j
    induction j with
    | zero =>
        intro _
        rw [pow_zero, hz0, Matrix.one_apply_eq]
        norm_num
    | succ j ih =>
        intro hj
        have hjlt : j < b := by omega
        have h1 := ih (by omega)
        have h2 : 0 < blockDynamics π blocks (zetaC blocks σ τ j) (zetaC blocks σ τ (j + 1)) := by
          refine blockDynamics_pos π hpos hb blocks ⟨j, hjlt⟩ _ _ ?_
          rw [mem_cyl]
          intro w hw
          have hiff : w ∈ upto blocks (j + 1) ↔ w ∈ upto blocks j := by
            rw [mem_upto, mem_upto]
            constructor
            · rintro ⟨i, hi, hwi⟩
              rcases (by omega : i.val < j ∨ i.val = j) with h | h
              · exact ⟨i, h, hwi⟩
              · exact absurd (by rw [show (⟨j, hjlt⟩ : Fin b) = i from Fin.ext h.symm]; exact hwi) hw
            · rintro ⟨i, hi, hwi⟩
              exact ⟨i, by omega, hwi⟩
          rw [zetaC, zetaC]
          by_cases hc : w ∈ upto blocks j
          · rw [if_pos (hiff.mpr hc), if_pos hc]
          · rw [if_neg (fun hcc => hc (hiff.mp hcc)), if_neg hc]
        exact pow_pos_step (blockDynamics π blocks) hst h1 h2
  have hfin := key b (le_refl _)
  rw [hzb] at hfin
  exact ⟨_, hfin⟩

end Blocks

section Ising

variable {Vv : Type*} [Fintype Vv] [DecidableEq Vv]
variable (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ)

/-- The integer spin `±1`. -/
private def sgnZ (b : Bool) : ℤ := if b then 1 else -1

private lemma spin_eq (σ : Vv → Bool) (v : Vv) : spin σ v = ((sgnZ (σ v) : ℤ) : ℝ) := by
  cases h : σ v <;> simp [spin, sgnZ, h]

/-- The integer local field `∑_{w ~ v} σ(w)`. -/
private def Sz (σ : Vv → Bool) (v : Vv) : ℤ :=
  ∑ w, if G.Adj v w then sgnZ (σ w) else 0

private lemma Sz_real (σ : Vv → Bool) (v : Vv) :
    ((Sz G σ v : ℤ) : ℝ) = ∑ w, if G.Adj v w then spin σ w else 0 := by
  simp only [Sz, Int.cast_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : G.Adj v w
  · rw [if_pos h, if_pos h, spin_eq]
  · rw [if_neg h, if_neg h, Int.cast_zero]
/-- The part of the energy not involving the site `v`. -/
private def offPart (σ : Vv → Bool) (v : Vv) : ℝ :=
  ∑ u ∈ univ.erase v, ∑ w ∈ univ.erase v, if G.Adj u w then spin σ u * spin σ w else 0

private lemma spin_update_ne (σ : Vv → Bool) (v : Vv) (s : Bool) {u : Vv} (h : u ≠ v) :
    spin (Function.update σ v s) u = spin σ u := by
  simp [spin, Function.update_apply, h]

private lemma spin_update_self (σ : Vv → Bool) (v : Vv) (s : Bool) :
    spin (Function.update σ v s) v = ((sgnZ s : ℤ) : ℝ) := by
  cases s <;> simp [spin, sgnZ]

private lemma offPart_update (σ : Vv → Bool) (v : Vv) (s : Bool) :
    offPart G (Function.update σ v s) v = offPart G σ v := by
  simp only [offPart]
  refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun w hw => ?_
  rw [spin_update_ne σ v s (Finset.ne_of_mem_erase hu),
    spin_update_ne σ v s (Finset.ne_of_mem_erase hw)]

private lemma energy_update (σ : Vv → Bool) (v : Vv) (s : Bool) :
    (∑ u : Vv, ∑ w : Vv, if G.Adj u w then
        spin (Function.update σ v s) u * spin (Function.update σ v s) w else 0)
      = 2 * ((sgnZ s : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ) + offPart G σ v := by
  classical
  set σ' := Function.update σ v s with hσ'
  set c : ℝ := ((sgnZ s : ℤ) : ℝ) with hc
  have hrow : ∀ u : Vv, u ≠ v →
      (∑ w : Vv, if G.Adj u w then spin σ' u * spin σ' w else 0)
        = (if G.Adj u v then spin σ u * c else 0)
          + ∑ w ∈ univ.erase v, (if G.Adj u w then spin σ u * spin σ w else 0) := by
    intro u hu
    rw [← Finset.add_sum_erase _
      (fun w => if G.Adj u w then spin σ' u * spin σ' w else 0) (Finset.mem_univ v)]
    congr 1
    · by_cases h : G.Adj u v
      · rw [if_pos h, if_pos h, spin_update_ne σ v s hu, hσ', spin_update_self]
      · rw [if_neg h, if_neg h]
    · refine Finset.sum_congr rfl fun w hw => ?_
      rw [spin_update_ne σ v s hu, spin_update_ne σ v s (Finset.ne_of_mem_erase hw)]
  have hv : (∑ w : Vv, if G.Adj v w then spin σ' v * spin σ' w else 0)
      = c * ((Sz G σ v : ℤ) : ℝ) := by
    rw [Sz_real, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h : G.Adj v w
    · have hwv : w ≠ v := fun hh => G.irrefl (hh ▸ h)
      rw [if_pos h, if_pos h, hσ', spin_update_self, spin_update_ne σ v s hwv]
    · rw [if_neg h, if_neg h, mul_zero]
  have hcol : (∑ u ∈ univ.erase v, if G.Adj u v then spin σ u * c else 0)
      = c * ((Sz G σ v : ℤ) : ℝ) := by
    rw [Sz_real, Finset.mul_sum]
    rw [← Finset.add_sum_erase _ (fun u => c * if G.Adj v u then spin σ u else 0)
      (Finset.mem_univ v)]
    have hvv : ¬ G.Adj v v := G.irrefl
    rw [if_neg hvv, mul_zero, zero_add]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h : G.Adj u v
    · rw [if_pos h, if_pos (G.symm h)]; ring
    · rw [if_neg h, if_neg (fun hh => h (G.symm hh)), mul_zero]
  rw [← Finset.add_sum_erase _
    (fun u => ∑ w : Vv, if G.Adj u w then spin σ' u * spin σ' w else 0) (Finset.mem_univ v)]
  rw [hv, Finset.sum_congr rfl (fun u hu => hrow u (Finset.ne_of_mem_erase hu)),
    Finset.sum_add_distrib, hcol]
  simp only [offPart]
  ring

private lemma weight_update (σ : Vv → Bool) (v : Vv) (s : Bool) :
    isingWeight G β (Function.update σ v s)
      = Real.exp (β * ((sgnZ s : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ))
        * Real.exp (β * 2⁻¹ * offPart G σ v) := by
  rw [isingWeight, energy_update, ← Real.exp_add]
  congr 1
  ring

private lemma isingWeight_pos (σ : Vv → Bool) : 0 < isingWeight G β σ := Real.exp_pos _

private lemma isingZ_pos : (0 : ℝ) < ∑ η : Vv → Bool, isingWeight G β η :=
  Finset.sum_pos (fun η _ => Real.exp_pos _) ⟨fun _ => true, Finset.mem_univ _⟩

private lemma isingDist_pos (σ : Vv → Bool) : 0 < isingDist G β σ := by
  rw [isingDist]
  exact div_pos (Real.exp_pos _) (isingZ_pos G β)

private lemma isingDist_isDist : IsDist (isingDist G β) := by
  refine ⟨fun σ => (isingDist_pos G β σ).le, ?_⟩
  simp only [isingDist]
  rw [← sum_div_const, div_self (ne_of_gt (isingZ_pos G β))]

private lemma update_self_eq (σ : Vv → Bool) (v : Vv) :
    Function.update σ v (σ v) = σ := by
  funext u
  rw [Function.update_apply]
  by_cases hu : u = v
  · rw [if_pos hu, hu]
  · rw [if_neg hu]

private lemma weight_self (σ : Vv → Bool) (v : Vv) :
    isingWeight G β σ
      = Real.exp (β * ((sgnZ (σ v) : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ))
        * Real.exp (β * 2⁻¹ * offPart G σ v) := by
  have h := weight_update G β σ v (σ v)
  rwa [update_self_eq] at h

private lemma Sz_abs_le (σ : Vv → Bool) (v : Vv) : |Sz G σ v| ≤ (G.degree v : ℤ) := by
  have hdeg : ((G.degree v : ℕ) : ℤ) = ∑ w : Vv, if G.Adj v w then (1 : ℤ) else 0 := by
    rw [← Finset.sum_filter]
    have hnb : (univ.filter fun w : Vv => G.Adj v w) = G.neighborFinset v := by
      ext w; simp [SimpleGraph.mem_neighborFinset]
    rw [hnb, Finset.sum_const, SimpleGraph.degree, nsmul_eq_mul, mul_one]
  rw [hdeg, Sz]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun w _ => ?_)
  by_cases h : G.Adj v w
  · rw [if_pos h, if_pos h]
    cases hw : σ w <;> simp [sgnZ]
  · rw [if_neg h, if_neg h]
    simp

private lemma sgnZ_abs (s : Bool) : |((sgnZ s : ℤ) : ℝ)| = 1 := by
  cases s <;> simp [sgnZ]

private lemma weight_update_le (hβ : 0 < β) (σ : Vv → Bool) (v : Vv) (s : Bool) :
    isingWeight G β (Function.update σ v s)
      ≤ Real.exp (2 * β * (G.maxDegree : ℝ)) * isingWeight G β σ := by
  rw [weight_update, weight_self G β σ v, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  set z : ℝ := ((Sz G σ v : ℤ) : ℝ) with hz
  have hzabs : |z| ≤ (G.maxDegree : ℝ) := by
    have h1 : |Sz G σ v| ≤ (G.degree v : ℤ) := Sz_abs_le G σ v
    have h2 : G.degree v ≤ G.maxDegree := G.degree_le_maxDegree v
    have h3 : |z| = ((|Sz G σ v| : ℤ) : ℝ) := by rw [hz]; push_cast [abs_eq_abs]; simp
    rw [h3]
    have : ((|Sz G σ v| : ℤ) : ℝ) ≤ ((G.degree v : ℤ) : ℝ) := by exact_mod_cast h1
    refine le_trans this ?_
    exact_mod_cast h2
  have hd : |((sgnZ s : ℤ) : ℝ) - ((sgnZ (σ v) : ℤ) : ℝ)| ≤ 2 := by
    have h1 : ((sgnZ s : ℤ) : ℝ) = 1 ∨ ((sgnZ s : ℤ) : ℝ) = -1 := by
      cases s <;> simp [sgnZ]
    have h2 : ((sgnZ (σ v) : ℤ) : ℝ) = 1 ∨ ((sgnZ (σ v) : ℤ) : ℝ) = -1 := by
      cases hb : σ v <;> simp [sgnZ]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> norm_num
  have hkey : β * ((sgnZ s : ℤ) : ℝ) * z - β * ((sgnZ (σ v) : ℤ) : ℝ) * z
      ≤ 2 * β * (G.maxDegree : ℝ) := by
    have hprod : |(((sgnZ s : ℤ) : ℝ) - ((sgnZ (σ v) : ℤ) : ℝ)) * z|
        ≤ 2 * (G.maxDegree : ℝ) := by
      rw [abs_mul]
      exact mul_le_mul hd hzabs (abs_nonneg _) (by norm_num)
    have hle := le_of_abs_le hprod
    have hmul := mul_le_mul_of_nonneg_left hle hβ.le
    nlinarith [hmul]
  linarith [hkey]

private lemma dist_update_le (hβ : 0 < β) (σ : Vv → Bool) (v : Vv) (s : Bool) :
    isingDist G β (Function.update σ v s)
      ≤ Real.exp (2 * β * (G.maxDegree : ℝ)) * isingDist G β σ := by
  simp only [isingDist, div_eq_mul_inv, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (weight_update_le G β hβ σ v s)
    (le_of_lt (inv_pos.mpr (isingZ_pos G β)))

private lemma dist_patch_le (hβ : 0 < β) (ζ α : Vv → Bool) (D : Finset Vv) :
    isingDist G β (fun v => if v ∈ D then ζ v else α v)
      ≤ Real.exp (2 * β * (G.maxDegree : ℝ) * (D.card : ℝ)) * isingDist G β α := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | @insert d D' hd ih =>
      have hfun : (fun v => if v ∈ insert d D' then ζ v else α v)
          = Function.update (fun v => if v ∈ D' then ζ v else α v) d (ζ d) := by
        funext u
        rw [Function.update_apply]
        by_cases hu : u = d
        · rw [if_pos hu, hu, if_pos (Finset.mem_insert_self d D')]
        · rw [if_neg hu]
          by_cases hv : u ∈ D'
          · rw [if_pos (Finset.mem_insert_of_mem hv), if_pos hv]
          · rw [if_neg (fun hc => by rcases Finset.mem_insert.mp hc with h | h
                                     · exact hu h
                                     · exact hv h), if_neg hv]
      rw [hfun]
      refine le_trans (dist_update_le G β hβ _ d (ζ d)) ?_
      refine le_trans (mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le) ?_
      rw [← mul_assoc, ← Real.exp_add, Finset.card_insert_of_notMem hd]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (isingDist_pos G β α).le
      push_cast
      ring_nf
      linarith

variable [Nonempty Vv]

private lemma patch_le_C (hβ : 0 < β) (ζ α : Vv → Bool) (D : Finset Vv) (M : ℕ)
    (hD : D.card ≤ M + 1) :
    isingDist G β (fun u => if u ∈ D then ζ u else α u)
      ≤ Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)) * isingDist G β α := by
  refine le_trans (dist_patch_le G β hβ ζ α D) ?_
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (isingDist_pos G β α).le
  have h1 : (D.card : ℝ) ≤ (M : ℝ) + 1 := by exact_mod_cast hD
  have h2 : (0 : ℝ) ≤ 2 * β * (G.maxDegree : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) hβ.le) (Nat.cast_nonneg _)
  nlinarith

/-- The single-site contribution at `v` to (twice) the Glauber Dirichlet form. -/
private def Dsite (f : (Vv → Bool) → ℝ) (v : Vv) : ℝ :=
  ∑ η : Vv → Bool, ∑ ρ : Vv → Bool,
    (f η - f ρ) ^ 2 * (isingDist G β η * blockUpdate (isingDist G β) ({v} : Finset Vv) η ρ)

private lemma Dsite_nonneg (f : (Vv → Bool) → ℝ) (v : Vv) : 0 ≤ Dsite G β f v := by
  refine Finset.sum_nonneg fun η _ => Finset.sum_nonneg fun ρ _ => ?_
  exact mul_nonneg (sq_nonneg _) (mul_nonneg (isingDist_pos G β η).le
    ((blockUpdate_stochastic (isingDist G β) (isingDist_pos G β) _).1 η ρ))

private lemma block_step (hβ : 0 < β) (f : (Vv → Bool) → ℝ) (W : Finset Vv) (M : ℕ)
    (hW : W.card ≤ M) {k : ℕ} (hk : k < W.card) :
    ∑ σ : Vv → Bool, ∑ τ : Vv → Bool,
        (f (mixc W σ τ k) - f (mixc W σ τ (k + 1))) ^ 2
          * (isingDist G β σ * blockUpdate (isingDist G β) W σ τ)
      ≤ ((2 : ℝ) ^ M * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))))
          * Dsite G β f (ste W k) := by
  classical
  have hpos := isingDist_pos G β
  have hC0 : (0 : ℝ) < Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)) := Real.exp_pos _
  have hixv : ixf W (ste W k) = k := ixf_ste W hk
  have hinv : ∀ η ζ : Vv → Bool, mixc W (mixc W η ζ k) (mixc W ζ η k) k = η := by
    intro η ζ
    exact congrArg Prod.fst (swp_invol W k (η, ζ))
  have hτv : ∀ η ζ : Vv → Bool, mixc W ζ η k (ste W k) = ζ (ste W k) := by
    intro η ζ
    rw [mixc, if_neg]
    rintro ⟨-, hlt⟩
    rw [hixv] at hlt
    exact absurd hlt (Nat.lt_irrefl k)
  have hsucc : ∀ η ζ : Vv → Bool,
      mixc W (mixc W η ζ k) (mixc W ζ η k) (k + 1)
        = Function.update η (ste W k) (ζ (ste W k)) := by
    intro η ζ
    rw [mixc_succ W _ _ hk, hinv η ζ, hτv η ζ]
  -- reindex the double sum by the exchange involution
  have hre : ∀ F : (Vv → Bool) → (Vv → Bool) → ℝ,
      ∑ σ : Vv → Bool, ∑ τ : Vv → Bool, F σ τ
        = ∑ η : Vv → Bool, ∑ ζ : Vv → Bool, F (mixc W η ζ k) (mixc W ζ η k) := by
    intro F
    have h1 : ∑ p : (Vv → Bool) × (Vv → Bool), F p.1 p.2
        = ∑ σ : Vv → Bool, ∑ τ : Vv → Bool, F σ τ :=
      Fintype.sum_prod_type (fun p => F p.1 p.2)
    have h2 : ∑ p : (Vv → Bool) × (Vv → Bool), F (mixc W p.1 p.2 k) (mixc W p.2 p.1 k)
        = ∑ η : Vv → Bool, ∑ ζ : Vv → Bool, F (mixc W η ζ k) (mixc W ζ η k) :=
      Fintype.sum_prod_type (fun p => F (mixc W p.1 p.2 k) (mixc W p.2 p.1 k))
    have h3 : ∑ p : (Vv → Bool) × (Vv → Bool), F (mixc W p.1 p.2 k) (mixc W p.2 p.1 k)
        = ∑ p : (Vv → Bool) × (Vv → Bool), F p.1 p.2 :=
      Fintype.sum_bijective (swp W k) (swp_invol W k).bijective _ _ (fun _ => rfl)
    rw [← h1, ← h2, h3]
  rw [hre]
  -- pointwise bound on the reindexed summand
  have hbody : ∀ η ζ : Vv → Bool,
      (f (mixc W (mixc W η ζ k) (mixc W ζ η k) k)
          - f (mixc W (mixc W η ζ k) (mixc W ζ η k) (k + 1))) ^ 2
          * (isingDist G β (mixc W η ζ k)
             * blockUpdate (isingDist G β) W (mixc W η ζ k) (mixc W ζ η k))
        ≤ (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)))
            * ((if ζ ∈ cyl W η then (1 : ℝ) else 0)
               * ((f η - f (Function.update η (ste W k) (ζ (ste W k)))) ^ 2
                  * (isingDist G β η
                     * blockUpdate (isingDist G β) ({ste W k} : Finset Vv) η
                         (Function.update η (ste W k) (ζ (ste W k)))))) := by
    intro η ζ
    rw [hinv η ζ, hsucc η ζ]
    by_cases hcy : ζ ∈ cyl W η
    · rw [if_pos hcy, one_mul]
      by_cases hne : Function.update η (ste W k) (ζ (ste W k)) = η
      · rw [hne]
        simp
      · have hmemρ : Function.update η (ste W k) (ζ (ste W k))
            ∈ cyl ({ste W k} : Finset Vv) η := by
          rw [mem_cyl]
          intro w hw
          rw [Function.update_apply, if_neg (by simpa using hw)]
        have hself : Function.update η (ste W k) (η (ste W k)) = η :=
          update_self_eq η (ste W k)
        have hzv : ζ (ste W k) ≠ η (ste W k) := by
          intro hc
          exact hne (by rw [hc]; exact hself)
        have hZv : ∑ ξ ∈ cyl ({ste W k} : Finset Vv) η, isingDist G β ξ
            = isingDist G β η
              + isingDist G β (Function.update η (ste W k) (ζ (ste W k))) := by
          rw [cyl_singleton_eq, Finset.sum_image (update_inj η (ste W k)), Fintype.sum_bool]
          cases hb : η (ste W k) with
          | false =>
              have h1 : Function.update η (ste W k) false = η := by rw [← hb]; exact hself
              have h2 : ζ (ste W k) = true := by
                cases hc : ζ (ste W k)
                · exact absurd (by rw [hc, hb]) hzv
                · rfl
              rw [h1, h2]
              ring
          | true =>
              have h1 : Function.update η (ste W k) true = η := by rw [← hb]; exact hself
              have h2 : ζ (ste W k) = false := by
                cases hc : ζ (ste W k)
                · rfl
                · exact absurd (by rw [hc, hb]) hzv
              rw [h1, h2]
              try ring
        have hb1 : isingDist G β (mixc W η ζ k)
            ≤ Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)) * isingDist G β η := by
          rw [mixc_patch W η ζ k]
          exact patch_le_C G β hβ ζ η _ M
            (le_trans (Finset.card_filter_le _ _) (by omega))
        have hb2 : isingDist G β (mixc W η ζ k)
            ≤ Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))
                * isingDist G β (Function.update η (ste W k) (ζ (ste W k))) := by
          rw [mixc_patch2 W η ζ hk]
          refine patch_le_C G β hβ _ _ _ M ?_
          have hcf := Finset.card_filter_le W (fun u => ixf W u < k)
          have hci := Finset.card_insert_le (ste W k) (W.filter (fun u => ixf W u < k))
          omega
        have hmin : isingDist G β (mixc W η ζ k)
            ≤ Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))
                * min (isingDist G β η)
                    (isingDist G β (Function.update η (ste W k) (ζ (ste W k)))) := by
          rcases le_total (isingDist G β η)
              (isingDist G β (Function.update η (ste W k) (ζ (ste W k)))) with h | h
          · rw [min_eq_left h]; exact hb1
          · rw [min_eq_right h]; exact hb2
        have hone : isingDist G β (mixc W η ζ k)
              * blockUpdate (isingDist G β) W (mixc W η ζ k) (mixc W ζ η k)
            ≤ isingDist G β (mixc W η ζ k) :=
          mul_le_of_le_one_right (hpos _).le
            (blockUpdate_le_one (isingDist G β) hpos W _ _)
        have hthree : Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))
              * min (isingDist G β η)
                  (isingDist G β (Function.update η (ste W k) (ζ (ste W k))))
            ≤ (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)))
                * (isingDist G β η
                   * blockUpdate (isingDist G β) ({ste W k} : Finset Vv) η
                       (Function.update η (ste W k) (ζ (ste W k)))) := by
          rw [blockUpdate_apply, if_pos hmemρ, hZv]
          have hmm := min_le_two_mul (isingDist G β η)
            (isingDist G β (Function.update η (ste W k) (ζ (ste W k)))) (hpos η) (hpos _)
          nlinarith [mul_le_mul_of_nonneg_left hmm hC0.le]
        have hXY : isingDist G β (mixc W η ζ k)
              * blockUpdate (isingDist G β) W (mixc W η ζ k) (mixc W ζ η k)
            ≤ (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)))
                * (isingDist G β η
                   * blockUpdate (isingDist G β) ({ste W k} : Finset Vv) η
                       (Function.update η (ste W k) (ζ (ste W k)))) :=
          le_trans hone (le_trans hmin hthree)
        calc (f η - f (Function.update η (ste W k) (ζ (ste W k)))) ^ 2
              * (isingDist G β (mixc W η ζ k)
                 * blockUpdate (isingDist G β) W (mixc W η ζ k) (mixc W ζ η k))
            ≤ (f η - f (Function.update η (ste W k) (ζ (ste W k)))) ^ 2
              * ((2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)))
                  * (isingDist G β η
                     * blockUpdate (isingDist G β) ({ste W k} : Finset Vv) η
                         (Function.update η (ste W k) (ζ (ste W k))))) :=
              mul_le_mul_of_nonneg_left hXY (sq_nonneg _)
          _ = (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)))
              * ((f η - f (Function.update η (ste W k) (ζ (ste W k)))) ^ 2
                 * (isingDist G β η
                    * blockUpdate (isingDist G β) ({ste W k} : Finset Vv) η
                        (Function.update η (ste W k) (ζ (ste W k))))) := by ring
    · rw [if_neg hcy, zero_mul, mul_zero]
      have hz : blockUpdate (isingDist G β) W (mixc W η ζ k) (mixc W ζ η k) = 0 := by
        rw [blockUpdate_apply, if_neg]
        intro hc
        exact hcy ((mixc_cyl_iff W η ζ k).mp hc)
      rw [hz, mul_zero, mul_zero]
  -- sum over ζ for fixed η
  have hstep : ∀ η : Vv → Bool,
      ∑ ζ : Vv → Bool,
        (f (mixc W (mixc W η ζ k) (mixc W ζ η k) k)
            - f (mixc W (mixc W η ζ k) (mixc W ζ η k) (k + 1))) ^ 2
            * (isingDist G β (mixc W η ζ k)
               * blockUpdate (isingDist G β) W (mixc W η ζ k) (mixc W ζ η k))
        ≤ ((2 : ℝ) ^ M * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))))
            * ∑ ρ : Vv → Bool, (f η - f ρ) ^ 2
                * (isingDist G β η
                   * blockUpdate (isingDist G β) ({ste W k} : Finset Vv) η ρ) := by
    intro η
    have hg : ∀ s : Bool, 0 ≤ (f η - f (Function.update η (ste W k) s)) ^ 2
        * (isingDist G β η
           * blockUpdate (isingDist G β) ({ste W k} : Finset Vv) η
               (Function.update η (ste W k) s)) := by
      intro s
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (hpos η).le
        ((blockUpdate_stochastic (isingDist G β) hpos _).1 _ _))
    have hcard : ((cyl W η).card : ℝ) ≤ (2 : ℝ) ^ M := by
      have h1 := card_cyl_le W η
      have h2 : (cyl W η).card ≤ 2 ^ M := by
        refine le_trans h1 ?_
        simpa using Nat.pow_le_pow_right (by norm_num) hW
      exact_mod_cast h2
    have hsum2 : ∑ s : Bool, (f η - f (Function.update η (ste W k) s)) ^ 2
          * (isingDist G β η
             * blockUpdate (isingDist G β) ({ste W k} : Finset Vv) η
                 (Function.update η (ste W k) s))
        ≤ ∑ ρ : Vv → Bool, (f η - f ρ) ^ 2
            * (isingDist G β η
               * blockUpdate (isingDist G β) ({ste W k} : Finset Vv) η ρ) :=
      sum_bool_update_le η (ste W k)
        (fun ρ => (f η - f ρ) ^ 2
          * (isingDist G β η
             * blockUpdate (isingDist G β) ({ste W k} : Finset Vv) η ρ))
        (fun ρ => mul_nonneg (sq_nonneg _) (mul_nonneg (hpos η).le
          ((blockUpdate_stochastic (isingDist G β) hpos _).1 _ _)))
    have hsum0 : (0 : ℝ) ≤ ∑ s : Bool, (f η - f (Function.update η (ste W k) s)) ^ 2
          * (isingDist G β η
             * blockUpdate (isingDist G β) ({ste W k} : Finset Vv) η
                 (Function.update η (ste W k) s)) :=
      Finset.sum_nonneg fun s _ => hg s
    calc ∑ ζ : Vv → Bool,
          (f (mixc W (mixc W η ζ k) (mixc W ζ η k) k)
              - f (mixc W (mixc W η ζ k) (mixc W ζ η k) (k + 1))) ^ 2
              * (isingDist G β (mixc W η ζ k)
                 * blockUpdate (isingDist G β) W (mixc W η ζ k) (mixc W ζ η k))
        ≤ ∑ ζ : Vv → Bool,
            (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)))
              * ((if ζ ∈ cyl W η then (1 : ℝ) else 0)
                 * ((f η - f (Function.update η (ste W k) (ζ (ste W k)))) ^ 2
                    * (isingDist G β η
                       * blockUpdate (isingDist G β) ({ste W k} : Finset Vv) η
                           (Function.update η (ste W k) (ζ (ste W k)))))) :=
          Finset.sum_le_sum fun ζ _ => hbody η ζ
      _ = (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)))
            * ∑ ζ ∈ cyl W η, (f η - f (Function.update η (ste W k) (ζ (ste W k)))) ^ 2
                * (isingDist G β η
                   * blockUpdate (isingDist G β) ({ste W k} : Finset Vv) η
                       (Function.update η (ste W k) (ζ (ste W k)))) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_congr rfl (fun ζ (_ : ζ ∈ Finset.univ) =>
            show (if ζ ∈ cyl W η then (1 : ℝ) else 0)
                * ((f η - f (Function.update η (ste W k) (ζ (ste W k)))) ^ 2
                   * (isingDist G β η
                      * blockUpdate (isingDist G β) ({ste W k} : Finset Vv) η
                          (Function.update η (ste W k) (ζ (ste W k)))))
              = if ζ ∈ cyl W η then
                  (f η - f (Function.update η (ste W k) (ζ (ste W k)))) ^ 2
                    * (isingDist G β η
                       * blockUpdate (isingDist G β) ({ste W k} : Finset Vv) η
                           (Function.update η (ste W k) (ζ (ste W k)))) else 0
              from by split_ifs <;> ring), ← Finset.sum_filter]
          congr 1
          ext ζ
          simp
      _ ≤ (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)))
            * (((cyl W η).card : ℝ)
               * ∑ s : Bool, (f η - f (Function.update η (ste W k) s)) ^ 2
                   * (isingDist G β η
                      * blockUpdate (isingDist G β) ({ste W k} : Finset Vv) η
                          (Function.update η (ste W k) s))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact sum_cyl_fiber W η (ste W k) _ hg
      _ ≤ (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)))
            * ((2 : ℝ) ^ M
               * ∑ ρ : Vv → Bool, (f η - f ρ) ^ 2
                   * (isingDist G β η
                      * blockUpdate (isingDist G β) ({ste W k} : Finset Vv) η ρ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hcard hsum2 hsum0 (by positivity)
      _ = ((2 : ℝ) ^ M * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))))
            * ∑ ρ : Vv → Bool, (f η - f ρ) ^ 2
                * (isingDist G β η
                   * blockUpdate (isingDist G β) ({ste W k} : Finset Vv) η ρ) := by ring
  refine le_trans (Finset.sum_le_sum fun η _ => hstep η) ?_
  rw [← Finset.mul_sum, Dsite]

private lemma sum_swap3 {α : Type*} (t : Finset α) (g : α → (Vv → Bool) → (Vv → Bool) → ℝ) :
    ∑ σ : Vv → Bool, ∑ τ : Vv → Bool, ∑ i ∈ t, g i σ τ
      = ∑ i ∈ t, ∑ σ : Vv → Bool, ∑ τ : Vv → Bool, g i σ τ := by
  rw [show (∑ σ : Vv → Bool, ∑ τ : Vv → Bool, ∑ i ∈ t, g i σ τ)
      = ∑ σ : Vv → Bool, ∑ i ∈ t, ∑ τ : Vv → Bool, g i σ τ from
    Finset.sum_congr rfl fun σ _ => Finset.sum_comm]
  exact Finset.sum_comm

private lemma telescope_cs (f : (Vv → Bool) → ℝ) (W : Finset Vv) (σ τ : Vv → Bool)
    (h : τ ∈ cyl W σ) :
    (f σ - f τ) ^ 2
      ≤ (W.card : ℝ) * ∑ k ∈ Finset.range W.card,
          (f (mixc W σ τ k) - f (mixc W σ τ (k + 1))) ^ 2 := by
  have hsum : ∑ k ∈ Finset.range W.card, (f (mixc W σ τ k) - f (mixc W σ τ (k + 1)))
      = f σ - f τ := by
    rw [Finset.sum_range_sub' (fun k => f (mixc W σ τ k)) W.card, mixc_zero,
      mixc_card W σ τ h]
  rw [← hsum]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range W.card)
      (f := fun k => f (mixc W σ τ k) - f (mixc W σ τ (k + 1)))
  simpa using hcs

private lemma pair_bound (f : (Vv → Bool) → ℝ) (W : Finset Vv) (M : ℕ)
    (hW : W.card ≤ M) (σ τ : Vv → Bool) :
    (f σ - f τ) ^ 2 * (isingDist G β σ * blockUpdate (isingDist G β) W σ τ)
      ≤ (M : ℝ) * ∑ k ∈ Finset.range W.card,
          ((f (mixc W σ τ k) - f (mixc W σ τ (k + 1))) ^ 2
            * (isingDist G β σ * blockUpdate (isingDist G β) W σ τ)) := by
  have hpos := isingDist_pos G β
  have hbu : 0 ≤ isingDist G β σ * blockUpdate (isingDist G β) W σ τ :=
    mul_nonneg (hpos σ).le ((blockUpdate_stochastic (isingDist G β) hpos W).1 σ τ)
  have hpull : (M : ℝ) * ∑ k ∈ Finset.range W.card,
        ((f (mixc W σ τ k) - f (mixc W σ τ (k + 1))) ^ 2
          * (isingDist G β σ * blockUpdate (isingDist G β) W σ τ))
      = ((M : ℝ) * ∑ k ∈ Finset.range W.card,
          (f (mixc W σ τ k) - f (mixc W σ τ (k + 1))) ^ 2)
        * (isingDist G β σ * blockUpdate (isingDist G β) W σ τ) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hpull]
  by_cases h : τ ∈ cyl W σ
  · refine mul_le_mul_of_nonneg_right ?_ hbu
    refine le_trans (telescope_cs f W σ τ h) ?_
    refine mul_le_mul_of_nonneg_right (by exact_mod_cast hW) ?_
    exact Finset.sum_nonneg fun k _ => sq_nonneg _
  · have hz : blockUpdate (isingDist G β) W σ τ = 0 := by
      rw [blockUpdate_apply, if_neg h]
    rw [hz, mul_zero, mul_zero, mul_zero]

private lemma block_bound (hβ : 0 < β) (f : (Vv → Bool) → ℝ) (W : Finset Vv) (M : ℕ)
    (hW : W.card ≤ M) :
    ∑ σ : Vv → Bool, ∑ τ : Vv → Bool,
        (f σ - f τ) ^ 2 * (isingDist G β σ * blockUpdate (isingDist G β) W σ τ)
      ≤ (M : ℝ) * ((2 : ℝ) ^ M * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))))
          * ∑ v ∈ W, Dsite G β f v := by
  classical
  have hA : ∑ σ : Vv → Bool, ∑ τ : Vv → Bool,
        (f σ - f τ) ^ 2 * (isingDist G β σ * blockUpdate (isingDist G β) W σ τ)
      ≤ ∑ σ : Vv → Bool, ∑ τ : Vv → Bool, ((M : ℝ) * ∑ k ∈ Finset.range W.card,
          ((f (mixc W σ τ k) - f (mixc W σ τ (k + 1))) ^ 2
            * (isingDist G β σ * blockUpdate (isingDist G β) W σ τ))) :=
    Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun τ _ => pair_bound G β f W M hW σ τ
  have hB : ∑ σ : Vv → Bool, ∑ τ : Vv → Bool, ((M : ℝ) * ∑ k ∈ Finset.range W.card,
        ((f (mixc W σ τ k) - f (mixc W σ τ (k + 1))) ^ 2
          * (isingDist G β σ * blockUpdate (isingDist G β) W σ τ)))
      = (M : ℝ) * ∑ k ∈ Finset.range W.card, ∑ σ : Vv → Bool, ∑ τ : Vv → Bool,
          ((f (mixc W σ τ k) - f (mixc W σ τ (k + 1))) ^ 2
            * (isingDist G β σ * blockUpdate (isingDist G β) W σ τ)) := by
    simp only [Finset.mul_sum]
    exact sum_swap3 (Finset.range W.card)
      (fun k σ τ => (M : ℝ) * ((f (mixc W σ τ k) - f (mixc W σ τ (k + 1))) ^ 2
        * (isingDist G β σ * blockUpdate (isingDist G β) W σ τ)))
  have hC : ∑ k ∈ Finset.range W.card, ∑ σ : Vv → Bool, ∑ τ : Vv → Bool,
        ((f (mixc W σ τ k) - f (mixc W σ τ (k + 1))) ^ 2
          * (isingDist G β σ * blockUpdate (isingDist G β) W σ τ))
      ≤ ∑ k ∈ Finset.range W.card,
          ((2 : ℝ) ^ M * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))))
            * Dsite G β f (ste W k) :=
    Finset.sum_le_sum fun k hk =>
      block_step G β hβ f W M hW (Finset.mem_range.mp hk)
  have hD : ∑ k ∈ Finset.range W.card,
        ((2 : ℝ) ^ M * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))))
          * Dsite G β f (ste W k)
      = ((2 : ℝ) ^ M * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))))
          * ∑ v ∈ W, Dsite G β f v := by
    rw [← Finset.mul_sum, sum_range_ste]
  calc ∑ σ : Vv → Bool, ∑ τ : Vv → Bool,
        (f σ - f τ) ^ 2 * (isingDist G β σ * blockUpdate (isingDist G β) W σ τ)
      ≤ _ := hA
    _ = (M : ℝ) * ∑ k ∈ Finset.range W.card, ∑ σ : Vv → Bool, ∑ τ : Vv → Bool,
          ((f (mixc W σ τ k) - f (mixc W σ τ (k + 1))) ^ 2
            * (isingDist G β σ * blockUpdate (isingDist G β) W σ τ)) := hB
    _ ≤ (M : ℝ) * ∑ k ∈ Finset.range W.card,
          ((2 : ℝ) ^ M * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))))
            * Dsite G β f (ste W k) :=
        mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg _)
    _ = (M : ℝ) * ((2 : ℝ) ^ M * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))))
          * ∑ v ∈ W, Dsite G β f v := by rw [hD]; ring

private lemma congestion (f : (Vv → Bool) → ℝ) {b : ℕ} (blocks : Fin b → Finset Vv)
    (Ms : ℕ) (hMs : ∀ v : Vv, (Finset.univ.filter fun i : Fin b => v ∈ blocks i).card ≤ Ms) :
    ∑ i : Fin b, ∑ v ∈ blocks i, Dsite G β f v
      ≤ (Ms : ℝ) * ∑ v : Vv, Dsite G β f v := by
  classical
  have h1 : ∀ i : Fin b, ∑ v ∈ blocks i, Dsite G β f v
      = ∑ v : Vv, if v ∈ blocks i then Dsite G β f v else 0 := by
    intro i
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hMs v) (Dsite_nonneg G β f v)

private lemma sum_Dsite (f : (Vv → Bool) → ℝ) :
    ∑ v : Vv, Dsite G β f v
      = (Fintype.card Vv : ℝ)
          * (2 * dirichletForm (glauber (isingDist G β)) (isingDist G β) f) := by
  have hN : (Fintype.card Vv : ℝ) ≠ 0 := by
    have : 0 < Fintype.card Vv := Fintype.card_pos
    positivity
  have hsw : ∑ v : Vv, ∑ η : Vv → Bool, ∑ ρ : Vv → Bool,
        (f η - f ρ) ^ 2
          * (isingDist G β η * blockUpdate (isingDist G β) ({v} : Finset Vv) η ρ)
      = ∑ η : Vv → Bool, ∑ ρ : Vv → Bool, ∑ v : Vv,
        (f η - f ρ) ^ 2
          * (isingDist G β η * blockUpdate (isingDist G β) ({v} : Finset Vv) η ρ) :=
    (sum_swap3 (Finset.univ : Finset Vv)
      (fun v η ρ => (f η - f ρ) ^ 2
        * (isingDist G β η * blockUpdate (isingDist G β) ({v} : Finset Vv) η ρ))).symm
  simp only [Dsite]
  rw [hsw, dirichletForm]
  have hinner : ∀ η ρ : Vv → Bool,
      (∑ v : Vv, (f η - f ρ) ^ 2
          * (isingDist G β η * blockUpdate (isingDist G β) ({v} : Finset Vv) η ρ))
        = (Fintype.card Vv : ℝ)
            * ((f η - f ρ) ^ 2 * (isingDist G β η * glauber (isingDist G β) η ρ)) := by
    intro η ρ
    have hg : (Fintype.card Vv : ℝ) * glauber (isingDist G β) η ρ
        = ∑ v : Vv, blockUpdate (isingDist G β) ({v} : Finset Vv) η ρ := by
      rw [glauber_eq_blocks, ← mul_assoc, mul_inv_cancel₀ hN, one_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [show (Fintype.card Vv : ℝ)
        * ((f η - f ρ) ^ 2 * (isingDist G β η * glauber (isingDist G β) η ρ))
        = (f η - f ρ) ^ 2 * (isingDist G β η
            * ((Fintype.card Vv : ℝ) * glauber (isingDist G β) η ρ)) from by ring, hg]
  rw [Finset.sum_congr rfl fun η _ => Finset.sum_congr rfl fun ρ _ => hinner η ρ]
  simp only [← Finset.mul_sum]
  ring

private lemma dirichlet_block_eq (f : (Vv → Bool) → ℝ) {b : ℕ} (blocks : Fin b → Finset Vv) :
    dirichletForm (blockDynamics (isingDist G β) blocks) (isingDist G β) f
      = 2⁻¹ * ((b : ℝ)⁻¹ * ∑ i : Fin b, ∑ σ : Vv → Bool, ∑ τ : Vv → Bool,
          (f σ - f τ) ^ 2
            * (isingDist G β σ * blockUpdate (isingDist G β) (blocks i) σ τ)) := by
  rw [dirichletForm]
  congr 1
  have hterm : ∀ σ τ : Vv → Bool,
      (f σ - f τ) ^ 2 * (isingDist G β σ * blockDynamics (isingDist G β) blocks σ τ)
        = ∑ i : Fin b, ((b : ℝ)⁻¹
            * ((f σ - f τ) ^ 2
               * (isingDist G β σ * blockUpdate (isingDist G β) (blocks i) σ τ))) := by
    intro σ τ
    rw [blockDynamics]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => hterm σ τ]
  rw [sum_swap3 (Finset.univ : Finset (Fin b))
    (fun i σ τ => (b : ℝ)⁻¹
      * ((f σ - f τ) ^ 2
         * (isingDist G β σ * blockUpdate (isingDist G β) (blocks i) σ τ)))]
  simp only [← Finset.mul_sum]

private lemma main_comparison (hβ : 0 < β) {b : ℕ} (hb : 0 < b)
    (blocks : Fin b → Finset Vv)
    (hcover : ∀ v : Vv, ∃ i : Fin b, v ∈ blocks i)
    (M Ms : ℕ) (hM : ∀ i : Fin b, (blocks i).card ≤ M)
    (hMs : ∀ v : Vv, (Finset.univ.filter fun i : Fin b => v ∈ blocks i).card ≤ Ms) :
    spectralGap (blockDynamics (isingDist G β) blocks) ≤
      (M : ℝ) ^ 2 * (Ms : ℝ) *
        (4 * Real.exp (2 * β * (G.maxDegree : ℝ))) ^ (M + 1) *
      spectralGap (glauber (isingDist G β)) := by
  classical
  have hpos := isingDist_pos G β
  have hdist := isingDist_isDist G β
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  obtain ⟨v0⟩ := ‹Nonempty Vv›
  obtain ⟨i0, hi0⟩ := hcover v0
  have hM1 : 1 ≤ M := le_trans (Finset.card_pos.mpr ⟨v0, hi0⟩) (hM i0)
  have hMs1 : 1 ≤ Ms := by
    refine le_trans ?_ (hMs v0)
    exact Finset.card_pos.mpr ⟨i0, by simp [hi0]⟩
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hMsR : (0 : ℝ) < (Ms : ℝ) := by exact_mod_cast hMs1
  have hNbM : Fintype.card Vv ≤ b * M := by
    have hsub : (Finset.univ : Finset Vv)
        ⊆ (Finset.univ : Finset (Fin b)).biUnion blocks := by
      intro v _
      obtain ⟨i, hi⟩ := hcover v
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩
    calc Fintype.card Vv = (Finset.univ : Finset Vv).card := (Finset.card_univ).symm
      _ ≤ ((Finset.univ : Finset (Fin b)).biUnion blocks).card := Finset.card_le_card hsub
      _ ≤ ∑ i : Fin b, (blocks i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin b, M := Finset.sum_le_sum fun i _ => hM i
      _ = b * M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hNb : (Fintype.card Vv : ℝ) ≤ (b : ℝ) * (M : ℝ) := by exact_mod_cast hNbM
  have hCpow : (4 * Real.exp (2 * β * (G.maxDegree : ℝ))) ^ (M + 1)
      = (4 : ℝ) ^ (M + 1) * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)) := by
    have hcast : ((M + 1 : ℕ) : ℝ) * (2 * β * (G.maxDegree : ℝ))
        = 2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1) := by push_cast; ring
    rw [mul_pow, ← Real.exp_nat_mul, hcast]
  set B : ℝ := (M : ℝ) ^ 2 * (Ms : ℝ)
      * (4 * Real.exp (2 * β * (G.maxDegree : ℝ))) ^ (M + 1) with hBdef
  have hB0 : 0 < B := by
    have h4 : (0 : ℝ) < 4 * Real.exp (2 * β * (G.maxDegree : ℝ)) := by positivity
    rw [hBdef]
    exact mul_pos (mul_pos (pow_pos hMR 2) hMsR) (pow_pos h4 (M + 1))
  have hgl := glauber_stationary (isingDist G β) hdist
  have hglS : IsStochastic (glauber (isingDist G β)) :=
    ⟨hgl.1, fun x => hgl.2.1 x (hpos x)⟩
  have hbdS : IsStochastic (blockDynamics (isingDist G β) blocks) :=
    blockDynamics_stochastic (isingDist G β) hpos hb blocks
  have hbdR : DetailedBalance (blockDynamics (isingDist G β) blocks) (isingDist G β) :=
    blockDynamics_reversible (isingDist G β) hpos blocks
  have hcomp : ∀ f : (Vv → Bool) → ℝ,
      dirichletForm (blockDynamics (isingDist G β) blocks) (isingDist G β) f
        ≤ B * dirichletForm (glauber (isingDist G β)) (isingDist G β) f := by
    intro f
    have hEG0 : 0 ≤ dirichletForm (glauber (isingDist G β)) (isingDist G β) f := by
      rw [dirichletForm]
      refine mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun η _ => Finset.sum_nonneg fun ρ _ => ?_)
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (hpos η).le (hglS.1 η ρ))
    have hK0 : (0 : ℝ) ≤ (M : ℝ)
        * ((2 : ℝ) ^ M * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)))) := by
      positivity
    have hS : ∑ i : Fin b, ∑ σ : Vv → Bool, ∑ τ : Vv → Bool,
          (f σ - f τ) ^ 2
            * (isingDist G β σ * blockUpdate (isingDist G β) (blocks i) σ τ)
        ≤ ((M : ℝ)
            * ((2 : ℝ) ^ M * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))))
            * (Ms : ℝ) * (Fintype.card Vv : ℝ) * 2)
          * dirichletForm (glauber (isingDist G β)) (isingDist G β) f := by
      calc ∑ i : Fin b, ∑ σ : Vv → Bool, ∑ τ : Vv → Bool,
            (f σ - f τ) ^ 2
              * (isingDist G β σ * blockUpdate (isingDist G β) (blocks i) σ τ)
          ≤ ∑ i : Fin b, ((M : ℝ)
              * ((2 : ℝ) ^ M
                 * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))))
              * ∑ v ∈ blocks i, Dsite G β f v) :=
            Finset.sum_le_sum fun i _ => block_bound G β hβ f (blocks i) M (hM i)
        _ = ((M : ℝ)
              * ((2 : ℝ) ^ M
                 * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)))))
            * ∑ i : Fin b, ∑ v ∈ blocks i, Dsite G β f v := by rw [← Finset.mul_sum]
        _ ≤ ((M : ℝ)
              * ((2 : ℝ) ^ M
                 * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)))))
            * ((Ms : ℝ) * ∑ v : Vv, Dsite G β f v) :=
            mul_le_mul_of_nonneg_left (congestion G β f blocks Ms hMs) hK0
        _ = ((M : ℝ)
              * ((2 : ℝ) ^ M
                 * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))))
              * (Ms : ℝ) * (Fintype.card Vv : ℝ) * 2)
            * dirichletForm (glauber (isingDist G β)) (isingDist G β) f := by
            rw [sum_Dsite]; ring
    have hpow : (2 : ℝ) * (2 : ℝ) ^ M ≤ (4 : ℝ) ^ (M + 1) := by
      have h1 : (2 : ℝ) ^ M ≤ (4 : ℝ) ^ M :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) M
      have h2 : (4 : ℝ) ^ (M + 1) = 4 * (4 : ℝ) ^ M := by rw [pow_succ]; ring
      have h3 : (0 : ℝ) ≤ (4 : ℝ) ^ M := by positivity
      linarith
    have hinv : (b : ℝ)⁻¹ * (Fintype.card Vv : ℝ) ≤ (M : ℝ) := by
      rw [← div_eq_inv_mul, div_le_iff₀ hbR]
      linarith
    have hcoef : 2⁻¹ * (b : ℝ)⁻¹
        * ((M : ℝ)
            * ((2 : ℝ) ^ M * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))))
            * (Ms : ℝ) * (Fintype.card Vv : ℝ) * 2) ≤ B := by
      have hX : (0 : ℝ) < Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)) :=
        Real.exp_pos _
      have hrest : (0 : ℝ) ≤ (M : ℝ) * ((2 : ℝ) * (2 : ℝ) ^ M) * (Ms : ℝ)
          * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)) := by positivity
      have hstep1 : 2⁻¹ * (b : ℝ)⁻¹
          * ((M : ℝ)
              * ((2 : ℝ) ^ M
                 * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))))
              * (Ms : ℝ) * (Fintype.card Vv : ℝ) * 2)
          = ((b : ℝ)⁻¹ * (Fintype.card Vv : ℝ))
            * ((M : ℝ) * ((2 : ℝ) * (2 : ℝ) ^ M) * (Ms : ℝ)
               * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))) := by ring
      rw [hstep1, hBdef, hCpow]
      have hA : ((b : ℝ)⁻¹ * (Fintype.card Vv : ℝ))
            * ((M : ℝ) * ((2 : ℝ) * (2 : ℝ) ^ M) * (Ms : ℝ)
               * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)))
          ≤ (M : ℝ)
            * ((M : ℝ) * ((2 : ℝ) * (2 : ℝ) ^ M) * (Ms : ℝ)
               * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_right hinv hrest
      refine le_trans hA ?_
      have hB2 : (M : ℝ) * ((2 : ℝ) * (2 : ℝ) ^ M) * (Ms : ℝ)
            * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))
          ≤ (M : ℝ) * ((4 : ℝ) ^ (M + 1)) * (Ms : ℝ)
            * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)) := by
        have hmm : (0 : ℝ) ≤ (M : ℝ) * (Ms : ℝ)
            * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)) := by positivity
        nlinarith [hpow, hmm]
      calc (M : ℝ)
            * ((M : ℝ) * ((2 : ℝ) * (2 : ℝ) ^ M) * (Ms : ℝ)
               * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1)))
          ≤ (M : ℝ)
            * ((M : ℝ) * ((4 : ℝ) ^ (M + 1)) * (Ms : ℝ)
               * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left hB2 hMR.le
        _ = (M : ℝ) ^ 2 * (Ms : ℝ)
            * ((4 : ℝ) ^ (M + 1)
               * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))) := by ring
    rw [dirichlet_block_eq]
    calc 2⁻¹ * ((b : ℝ)⁻¹ * ∑ i : Fin b, ∑ σ : Vv → Bool, ∑ τ : Vv → Bool,
          (f σ - f τ) ^ 2
            * (isingDist G β σ * blockUpdate (isingDist G β) (blocks i) σ τ))
        ≤ 2⁻¹ * ((b : ℝ)⁻¹ * (((M : ℝ)
              * ((2 : ℝ) ^ M
                 * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))))
              * (Ms : ℝ) * (Fintype.card Vv : ℝ) * 2)
            * dirichletForm (glauber (isingDist G β)) (isingDist G β) f)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS (by positivity))
            (by norm_num)
      _ = (2⁻¹ * (b : ℝ)⁻¹ * ((M : ℝ)
              * ((2 : ℝ) ^ M
                 * (2 * Real.exp (2 * β * (G.maxDegree : ℝ) * ((M : ℝ) + 1))))
              * (Ms : ℝ) * (Fintype.card Vv : ℝ) * 2))
            * dirichletForm (glauber (isingDist G β)) (isingDist G β) f := by ring
      _ ≤ B * dirichletForm (glauber (isingDist G β)) (isingDist G β) f :=
          mul_le_mul_of_nonneg_right hcoef hEG0
  have hV : 2 ≤ Fintype.card (Vv → Bool) := by
    have hN1 : 1 ≤ Fintype.card Vv := Fintype.card_pos
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Fintype.card Vv := Nat.pow_le_pow_right (by norm_num) hN1
      _ = Fintype.card (Vv → Bool) := by rw [Fintype.card_fun]; norm_num
  have hirrG : Irreducible (glauber (isingDist G β)) :=
    glauber_irred (isingDist G β) hpos
  have hirrB : Irreducible (blockDynamics (isingDist G β) blocks) :=
    blockDynamics_irred (isingDist G β) hpos hb blocks hcover
  obtain ⟨-, f0, hf1, hf2, hf3⟩ := dirichlet_gap hV (glauber (isingDist G β)) hglS hirrG
    (isingDist G β) hgl.2.2.2 hgl.2.2.1
  obtain ⟨hinf', -⟩ := dirichlet_gap hV (blockDynamics (isingDist G β) blocks) hbdS hirrB
    (isingDist G β) (stationary_of_reversible _ hbdS (isingDist G β) hdist hbdR) hbdR
  rw [hinf', hf3]
  refine le_trans (csInf_le ?_ ⟨f0, hf1, hf2, rfl⟩) (hcomp f0)
  refine ⟨0, ?_⟩
  rintro e ⟨g, -, -, rfl⟩
  rw [dirichletForm]
  refine mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_)
  exact mul_nonneg (sq_nonneg _) (mul_nonneg (hpos x).le (hbdS.1 x y))

end Ising

end

end MarkovMixing

open MarkovMixing

/-- **Theorem 15.9** (LPW): comparison of the block dynamics and the
single-site Glauber dynamics for the Ising model: if the blocks cover the
vertex set, have size at most `M`, and each vertex lies in at most `M⋆`
blocks, then `γ_B ≤ M² M⋆ (4 e^{2βΔ})^{M+1} γ`. -/
theorem solution {Vv : Type*} [Fintype Vv] [DecidableEq Vv]
    [Nonempty Vv] (G : SimpleGraph Vv) [DecidableRel G.Adj]
    (β : ℝ) (hβ : 0 < β) {b : ℕ} (hb : 0 < b) (blocks : Fin b → Finset Vv)
    (hcover : ∀ v : Vv, ∃ i : Fin b, v ∈ blocks i)
    (M Ms : ℕ) (hM : ∀ i : Fin b, (blocks i).card ≤ M)
    (hMs : ∀ v : Vv, (Finset.univ.filter fun i : Fin b => v ∈ blocks i).card ≤ Ms) :
    spectralGap (blockDynamics (isingDist G β) blocks) ≤
      (M : ℝ) ^ 2 * (Ms : ℝ) *
        (4 * Real.exp (2 * β * (G.maxDegree : ℝ))) ^ (M + 1) *
      spectralGap (glauber (isingDist G β)) :=
  main_comparison G β hβ hb blocks hcover M Ms hM hMs
