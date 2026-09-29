-- Prove2me | solution 1 for bool_func_alternating_sum_sensitivity
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-05-06T22:10:36.651172+00:00
-- url     : https://prove2.me/submissions/58a61614-cb4f-49b3-bcfb-8b10916bddcb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_bool_func_alternating_sum_sensitivity
import Theorems.Thm_cube_alt_sum_to_sensitivity_univ
import Definitions.Def_BoolFunc
import Definitions.Def_Hypercube
import Definitions.Def_sensitivity
import Definitions.Def_Mobius
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

open Mobius Finset

/-!
# Proof — `bool_func_alternating_sum_sensitivity`

Bridges `(f : BoolFunc n, S : Finset (Fin n))` to the d-cube case:
- Restrict `f` to the `S`-subcube via `Finset.orderIsoOfFin` to get
  `g : BoolFunc S.card`.
- Reindex the alt-sum on `S` to the alt-sum on `Finset.univ` over
  `Fin S.card`, via `T ↔ T.image e`.
- Apply the middle-layer theorem `cube_alt_sum_to_sensitivity_univ`
  to obtain `h S.card ≤ sensitivity g`.
- Lift sensitivity from `g` to `f` using
  `extendToCube (flipBit w i) = flipBit (extendToCube w) (e i)`.
-/

namespace BoolFuncAltSum

variable {n : ℕ}

/-- Extend a function on `Fin S.card` to `Fin n`, sending coordinates
    outside `S` to `false`. Inside `S`, look up the `Fin S.card`-index
    via the order-iso. -/
noncomputable def extendToCube (S : Finset (Fin n)) (w : Fin S.card → Bool) :
    Fin n → Bool :=
  fun i => if h : i ∈ S then w ((S.orderIsoOfFin rfl).symm ⟨i, h⟩) else false

@[simp] lemma extendToCube_apply_mem (S : Finset (Fin n)) (w : Fin S.card → Bool)
    {i : Fin n} (h : i ∈ S) :
    extendToCube S w i = w ((S.orderIsoOfFin rfl).symm ⟨i, h⟩) := by
  simp [extendToCube, h]

@[simp] lemma extendToCube_apply_notMem (S : Finset (Fin n)) (w : Fin S.card → Bool)
    {i : Fin n} (h : i ∉ S) :
    extendToCube S w i = false := by
  simp [extendToCube, h]

/-- The order embedding's image is in `S`. -/
lemma orderEmbOfFin_mem (S : Finset (Fin n)) (j : Fin S.card) :
    S.orderEmbOfFin rfl j ∈ S := S.orderEmbOfFin_mem rfl j

/-- The order embedding is the underlying map of the order iso. -/
lemma orderEmbOfFin_eq_orderIsoOfFin_val (S : Finset (Fin n)) (j : Fin S.card) :
    S.orderEmbOfFin rfl j = ((S.orderIsoOfFin rfl) j : Fin n) :=
  (Finset.coe_orderIsoOfFin_apply S rfl j).symm

/-- `extendToCube` and `boolOfFinset` are compatible under T ↦ T.image e. -/
lemma extendToCube_boolOfFinset
    (S : Finset (Fin n)) (T' : Finset (Fin S.card)) :
    extendToCube S (Mobius.boolOfFinset T')
    = Mobius.boolOfFinset (T'.image (S.orderEmbOfFin rfl)) := by
  classical
  funext j
  by_cases hj : j ∈ S
  · rw [extendToCube_apply_mem _ _ hj]
    simp only [Mobius.boolOfFinset_apply]
    by_cases h_in : (S.orderIsoOfFin rfl).symm ⟨j, hj⟩ ∈ T'
    · rw [decide_eq_true h_in]
      symm
      apply decide_eq_true
      refine Finset.mem_image.mpr ⟨_, h_in, ?_⟩
      rw [orderEmbOfFin_eq_orderIsoOfFin_val]
      have : ((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨j, hj⟩) : Fin n) = j := by
        rw [OrderIso.apply_symm_apply]
      exact this
    · rw [decide_eq_false h_in]
      symm
      apply decide_eq_false
      intro h_image
      apply h_in
      obtain ⟨i', hi'_T', hi'_eq⟩ := Finset.mem_image.mp h_image
      rw [orderEmbOfFin_eq_orderIsoOfFin_val] at hi'_eq
      have h_eq : (S.orderIsoOfFin rfl) i' = ⟨j, hj⟩ :=
        Subtype.ext hi'_eq
      rw [show (S.orderIsoOfFin rfl).symm ⟨j, hj⟩ = i' from by
        rw [← h_eq]; exact OrderIso.symm_apply_apply _ _]
      exact hi'_T'
  · rw [extendToCube_apply_notMem _ _ hj]
    simp only [Mobius.boolOfFinset_apply]
    have : j ∉ T'.image (S.orderEmbOfFin rfl) := by
      intro h_in
      obtain ⟨i', _, hi'_eq⟩ := Finset.mem_image.mp h_in
      have h_es : S.orderEmbOfFin rfl i' ∈ S := orderEmbOfFin_mem S i'
      rw [hi'_eq] at h_es
      exact hj h_es
    rw [decide_eq_false this]

/-- Cardinality of `T'.image e` equals `T'.card`. -/
@[simp] lemma card_image_orderEmbOfFin
    (S : Finset (Fin n)) (T' : Finset (Fin S.card)) :
    (T'.image (S.orderEmbOfFin rfl)).card = T'.card := by
  apply Finset.card_image_of_injective
  exact (S.orderEmbOfFin rfl).injective

/-- Image of `e` lands in `S`. -/
lemma image_orderEmbOfFin_subset
    (S : Finset (Fin n)) (T' : Finset (Fin S.card)) :
    T'.image (S.orderEmbOfFin rfl) ⊆ S := by
  intro x hx
  obtain ⟨i', _, rfl⟩ := Finset.mem_image.mp hx
  exact orderEmbOfFin_mem S i'

/-- Preimage of T ⊆ S along e gives a Finset (Fin S.card). -/
noncomputable def preimageS {S : Finset (Fin n)} (T : Finset (Fin n)) :
    Finset (Fin S.card) :=
  (Finset.univ : Finset (Fin S.card)).filter
    (fun i => S.orderEmbOfFin rfl i ∈ T)

lemma preimageS_image_eq_of_subset {S : Finset (Fin n)} {T : Finset (Fin n)}
    (hT : T ⊆ S) :
    (preimageS (S := S) T).image (S.orderEmbOfFin rfl) = T := by
  classical
  ext x
  simp only [preimageS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i', hi'_in_T, rfl⟩
    exact hi'_in_T
  · intro hx_T
    have hx_S : x ∈ S := hT hx_T
    refine ⟨(S.orderIsoOfFin rfl).symm ⟨x, hx_S⟩, ?_, ?_⟩
    · rw [orderEmbOfFin_eq_orderIsoOfFin_val]
      have : ↑((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨x, hx_S⟩)) = x := by
        rw [OrderIso.apply_symm_apply]
      rw [this]
      exact hx_T
    · rw [orderEmbOfFin_eq_orderIsoOfFin_val]
      have : ↑((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨x, hx_S⟩)) = x := by
        rw [OrderIso.apply_symm_apply]
      exact this

lemma image_preimageS_eq (S : Finset (Fin n)) (T' : Finset (Fin S.card)) :
    preimageS (S := S) (T'.image (S.orderEmbOfFin rfl)) = T' := by
  classical
  ext i
  simp only [preimageS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨i', hi'_in_T', hi'_eq⟩
    rw [show i = i' from (S.orderEmbOfFin rfl).injective hi'_eq.symm]
    exact hi'_in_T'
  · intro hi_in_T'
    exact ⟨i, hi_in_T', rfl⟩

@[simp] lemma card_preimageS_of_subset {S : Finset (Fin n)} {T : Finset (Fin n)}
    (hT : T ⊆ S) :
    (preimageS (S := S) T).card = T.card := by
  rw [← preimageS_image_eq_of_subset hT, card_image_orderEmbOfFin]
  rw [preimageS_image_eq_of_subset hT]

/-- `(S.orderIsoOfFin rfl).symm ⟨e i, _⟩ = i`. -/
lemma orderIsoOfFin_symm_orderEmbOfFin
    (S : Finset (Fin n)) (i : Fin S.card) (h : S.orderEmbOfFin rfl i ∈ S) :
    (S.orderIsoOfFin rfl).symm ⟨S.orderEmbOfFin rfl i, h⟩ = i := by
  have h_eq : (S.orderIsoOfFin rfl) i =
              ⟨S.orderEmbOfFin rfl i, h⟩ := by
    apply Subtype.ext
    exact (orderEmbOfFin_eq_orderIsoOfFin_val S i).symm
  rw [← h_eq]
  exact OrderIso.symm_apply_apply _ _

/-- Sensitivity-lift: `extendToCube` commutes with `flipBit` (at `e i`). -/
lemma extendToCube_flipBit (S : Finset (Fin n)) (w : Fin S.card → Bool) (i : Fin S.card) :
    extendToCube S (flipBit w i) = flipBit (extendToCube S w) (S.orderEmbOfFin rfl i) := by
  classical
  funext j
  set e := S.orderEmbOfFin rfl with e_def
  have h_e_in_S : e i ∈ S := orderEmbOfFin_mem S i
  by_cases hj_S : j ∈ S
  · rw [extendToCube_apply_mem _ _ hj_S]
    by_cases hj_e : j = e i
    · -- j = e i, so symm ⟨j, hj_S⟩ = i.
      have h_symm_eq : (S.orderIsoOfFin rfl).symm ⟨j, hj_S⟩ = i := by
        subst hj_e
        exact orderIsoOfFin_symm_orderEmbOfFin S i hj_S
      rw [h_symm_eq]
      unfold flipBit
      rw [Function.update_self]
      subst hj_e
      rw [Function.update_self]
      rw [extendToCube_apply_mem _ _ h_e_in_S]
      rw [orderIsoOfFin_symm_orderEmbOfFin S i h_e_in_S]
    · -- j ∈ S, j ≠ e i. Show symm ⟨j, hj_S⟩ ≠ i.
      have h_symm_ne : (S.orderIsoOfFin rfl).symm ⟨j, hj_S⟩ ≠ i := by
        intro h_eq
        apply hj_e
        have h_app : (S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨j, hj_S⟩) =
                     (S.orderIsoOfFin rfl) i := by rw [h_eq]
        rw [OrderIso.apply_symm_apply] at h_app
        have h_val : (((S.orderIsoOfFin rfl) i : ↑S) : Fin n) = j := by
          rw [← h_app]
        rw [orderEmbOfFin_eq_orderIsoOfFin_val S i] at *
        exact h_val.symm
      unfold flipBit
      rw [Function.update_of_ne h_symm_ne]
      rw [Function.update_of_ne hj_e]
      rw [extendToCube_apply_mem _ _ hj_S]
  · rw [extendToCube_apply_notMem _ _ hj_S]
    have hj_ne_e : j ≠ e i := by
      intro h_eq; apply hj_S; rw [h_eq]; exact h_e_in_S
    unfold flipBit
    rw [Function.update_of_ne hj_ne_e]
    rw [extendToCube_apply_notMem _ _ hj_S]

/-- For each `w : Fin S.card → Bool`, `sensitivityAt g w ≤ sensitivityAt f (extendToCube S w)`. -/
lemma sensitivityAt_le (f : BoolFunc n) (S : Finset (Fin n)) (w : Fin S.card → Bool) :
    sensitivityAt (fun w' => f (extendToCube S w')) w
    ≤ sensitivityAt f (extendToCube S w) := by
  classical
  unfold sensitivityAt
  apply Finset.card_le_card_of_injOn (fun i => S.orderEmbOfFin rfl i)
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter] at hi
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨_, hi'⟩ := hi
    show f (flipBit (extendToCube S w) (S.orderEmbOfFin rfl i)) ≠ f (extendToCube S w)
    rw [← extendToCube_flipBit]
    exact hi'
  · intros i _ j _ h
    exact (S.orderEmbOfFin rfl).injective h

end BoolFuncAltSum

theorem solution
    (h : ℕ → ℝ) (hmono : Monotone h)
    (hQ : ∀ m, 0 < m → ∀ S : Finset (Fin m → Bool),
        2 ^ (m - 1) < S.card →
          ∃ v ∈ S, h m ≤ (Hypercube.degreeIn m S v : ℝ))
    {n : ℕ} (f : BoolFunc n) (S : Finset (Fin n))
    (h_pos : 1 ≤ S.card)
    (h_alt :
      (∑ T ∈ S.powerset,
          (if (S.card - T.card) % 2 = 0 then (1 : ℝ) else -1) *
          (if f (fun i => decide (i ∈ T)) then (1 : ℝ) else 0))
        ≠ 0) :
    h S.card ≤ (sensitivity f : ℝ) := by
  classical
  -- Define g : BoolFunc S.card.
  let g : BoolFunc S.card := fun w => f (BoolFuncAltSum.extendToCube S w)
  -- Step 1: alt-sum on S of f equals alt-sum on univ of g.
  have h_alt_g :
      (∑ T' ∈ (Finset.univ : Finset (Fin S.card)).powerset,
          (if (S.card - T'.card) % 2 = 0 then (1 : ℝ) else -1) *
          (if g (fun i => decide (i ∈ T')) then (1 : ℝ) else 0))
        ≠ 0 := by
    rw [show (∑ T' ∈ (Finset.univ : Finset (Fin S.card)).powerset,
              (if (S.card - T'.card) % 2 = 0 then (1 : ℝ) else -1) *
              (if g (fun i => decide (i ∈ T')) then (1 : ℝ) else 0))
          = ∑ T ∈ S.powerset,
              (if (S.card - T.card) % 2 = 0 then (1 : ℝ) else -1) *
              (if f (fun i => decide (i ∈ T)) then (1 : ℝ) else 0) from ?_]
    · exact h_alt
    refine Finset.sum_bij'
      (fun T' _ => T'.image (S.orderEmbOfFin rfl))
      (fun T _ => BoolFuncAltSum.preimageS (S := S) T) ?_ ?_ ?_ ?_ ?_
    · intro T' _
      exact Finset.mem_powerset.mpr (BoolFuncAltSum.image_orderEmbOfFin_subset S T')
    · intro T hT
      exact Finset.mem_powerset.mpr (Finset.subset_univ _)
    · intro T' _
      exact BoolFuncAltSum.image_preimageS_eq S T'
    · intro T hT
      exact BoolFuncAltSum.preimageS_image_eq_of_subset (Finset.mem_powerset.mp hT)
    · intro T' _
      rw [BoolFuncAltSum.card_image_orderEmbOfFin]
      congr 1
      -- Goal: (if g (boolOfFinset T') then ... else ...) = (if f (boolOfFinset (T'.image e)) then ... else ...)
      have h_eq : g (fun i => decide (i ∈ T'))
                = f (fun j => decide (j ∈ T'.image (S.orderEmbOfFin rfl))) := by
        show f (BoolFuncAltSum.extendToCube S (fun i => decide (i ∈ T')))
              = f (fun j => decide (j ∈ T'.image (S.orderEmbOfFin rfl)))
        congr 1
        have : BoolFuncAltSum.extendToCube S (Mobius.boolOfFinset T')
              = Mobius.boolOfFinset (T'.image (S.orderEmbOfFin rfl)) :=
          BoolFuncAltSum.extendToCube_boolOfFinset S T'
        unfold Mobius.boolOfFinset at this
        exact this
      rw [h_eq]
  -- Step 2: apply cube_alt_sum_to_sensitivity_univ.
  have h_g_bound : h S.card ≤ (sensitivity g : ℝ) :=
    cube_alt_sum_to_sensitivity_univ h hmono hQ h_pos g h_alt_g
  -- Step 3: sensitivity g ≤ sensitivity f.
  have h_lift : sensitivity g ≤ sensitivity f := by
    unfold sensitivity
    apply Finset.sup_le
    intros w _
    calc sensitivityAt g w
        ≤ sensitivityAt f (BoolFuncAltSum.extendToCube S w) :=
          BoolFuncAltSum.sensitivityAt_le f S w
      _ ≤ Finset.univ.sup (sensitivityAt f) :=
          Finset.le_sup (Finset.mem_univ _)
  calc (h S.card : ℝ)
      ≤ (sensitivity g : ℝ) := h_g_bound
    _ ≤ (sensitivity f : ℝ) := by exact_mod_cast h_lift
