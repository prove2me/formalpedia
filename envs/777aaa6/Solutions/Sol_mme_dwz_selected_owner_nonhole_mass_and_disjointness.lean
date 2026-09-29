-- Prove2me | solution 1 for mme_dwz_selected_owner_nonhole_mass_and_disjointness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T15:14:27.466245+00:00
-- url     : https://prove2.me/submissions/1aae177a-9110-41fb-9f44-da24aef44dfe

import Definitions.Def_mme_dwz_selected_owner_nonhole_data
import Theorems.Thm_mme_dwz_joint_hash_ambient_xy_isolation_nonhole_mass
import Mathlib.Data.Finset.Prod

open BigOperators MME.DWZOwnerMass
set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZOwnerMass
variable {State Edge Block X Y Z : Type*}
variable [Fintype State] [Nonempty State] [DecidableEq State]
variable [Fintype Edge] [DecidableEq Edge]
variable [Fintype Block] [DecidableEq Block]
variable [DecidableEq X] [DecidableEq Y]

omit [Fintype State] [Nonempty State] [Fintype Edge] [DecidableEq Edge]
  [DecidableEq X] [DecidableEq Y] in
theorem selected_spec (targets ambient : Finset Edge)
    (events : Edge → Finset State) (x : Edge → X) (y : Edge → Y)
    (w : State) (a : Edge) (ha : a ∈ selected targets ambient events x y w) :
    a ∈ targets ∧ w ∈ events a ∧ Isolated ambient events x y w a := by
  classical
  exact Finset.mem_filter.mp ha

omit [Fintype State] [Nonempty State] [Fintype Edge] [DecidableEq Edge]
  [DecidableEq X] [DecidableEq Y] in
theorem selected_xy_injective (targets ambient : Finset Edge)
    (events : Edge → Finset State) (x : Edge → X) (y : Edge → Y)
    (hsub : targets ⊆ ambient) (w : State) :
    Set.InjOn x (selected targets ambient events x y w : Set Edge) ∧
      Set.InjOn y (selected targets ambient events x y w : Set Edge) := by
  constructor
  · intro a ha b hb hab
    obtain ⟨_, _, hiso⟩ := selected_spec targets ambient events x y w b hb
    obtain ⟨haT, haE, _⟩ := selected_spec targets ambient events x y w a ha
    exact hiso a (hsub haT) haE (Or.inl hab)
  · intro a ha b hb hab
    obtain ⟨_, _, hiso⟩ := selected_spec targets ambient events x y w b hb
    obtain ⟨haT, haE, _⟩ := selected_spec targets ambient events x y w a ha
    exact hiso a (hsub haT) haE (Or.inr hab)

omit [DecidableEq Block] in
/-- The surviving fine Z variables cannot belong to two different owners.
Self-compatibility is supplied by usefulness, not assumed coefficient isolation.
-/
theorem nonhole_image_owner_unique (owners : Finset Edge)
    (embed : Edge → Block → Z) (compatible : Z → Edge → Prop)
    (hself : ∀ a ∈ owners, ∀ z, compatible (embed a z) a)
    (a b : Edge) (hb : b ∈ owners) (u v : Block)
    (hu : u ∈ nonholes owners embed compatible a)
    (heq : embed a u = embed b v) : b = a := by
  classical
  have huniq := (Finset.mem_filter.mp hu).2
  exact huniq b hb (heq ▸ hself b hb v)

/-- Convert the mass bound into a sum of actual surviving block counts.
The same state is used for all owners, both kinds of deletions, and all blocks.
-/
theorem exists_selected_nonhole_mass
    (targets ambient : Finset Edge) (events : Edge → Finset State)
    (x : Edge → X) (y : Edge → Y)
    (embed : Edge → Block → Z) (compatible : Z → Edge → Prop)
    (K J p d c : ℕ) (hK : K = p * J)
    (hxyBudget : 4 * d ≤ p) (hzBudget : 8 * c ≤ p)
    (hsingle : ∀ a ∈ targets, (events a).card = K)
    (hx : ∀ a ∈ targets, (ambient.filter (fun b ↦ x b = x a)).card ≤ d)
    (hy : ∀ a ∈ targets, (ambient.filter (fun b ↦ y b = y a)).card ≤ d)
    (hzCard : ∀ a ∈ targets, ∀ z,
      (competitors targets embed compatible a z).card ≤ c)
    (hxyPair : ∀ a ∈ targets, ∀ b ∈ ambient,
      b ≠ a → (x b = x a ∨ y b = y a) →
        (events a ∩ events b).card ≤ J)
    (hzPair : ∀ a ∈ targets, ∀ z, ∀ b ∈ competitors targets embed compatible a z,
      (events a ∩ events b).card ≤ J) :
    ∃ w : State,
      3 * (targets.card * Fintype.card Block * K) ≤
        8 * (Fintype.card State *
          ∑ a ∈ selected targets ambient events x y w,
            (nonholes (selected targets ambient events x y w) embed compatible a).card) := by
  classical
  obtain ⟨w, hw⟩ := mme_dwz_joint_hash_ambient_xy_isolation_nonhole_mass
    targets ambient events x y (competitors targets embed compatible)
    K J p d c hK hxyBudget hzBudget hsingle hx hy hzCard hxyPair hzPair
  let owners := selected targets ambient events x y w
  let good := (targets.product (Finset.univ : Finset Block)).filter (fun az ↦
    w ∈ events az.1 ∧ Isolated ambient events x y w az.1 ∧
      ∀ b ∈ competitors targets embed compatible az.1 az.2, w ∉ events b)
  let actual := (owners.product (Finset.univ : Finset Block)).filter (fun az ↦
    az.2 ∈ nonholes owners embed compatible az.1)
  have hsub : good ⊆ actual := by
    intro az haz
    obtain ⟨hazT, haE, haI, haZ⟩ := Finset.mem_filter.mp haz
    have ha : az.1 ∈ owners :=
      Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hazT).1, haE, haI⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, Finset.mem_univ _⟩, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro b hb hcompat
    by_contra hne
    obtain ⟨hbT, hbE, _⟩ := selected_spec targets ambient events x y w b hb
    exact haZ b (Finset.mem_filter.mpr ⟨hbT, hne, hcompat⟩) hbE
  have hcard : actual.card = ∑ a ∈ owners, (nonholes owners embed compatible a).card := by
    calc
      actual.card = (owners.sigma (fun a ↦ nonholes owners embed compatible a)).card := by
        apply Finset.card_bij (fun az _ ↦ (⟨az.1, az.2⟩ : (a : Edge) × Block))
        · intro az haz
          obtain ⟨haz, hu⟩ := Finset.mem_filter.mp haz
          exact Finset.mem_sigma.mpr ⟨(Finset.mem_product.mp haz).1, hu⟩
        · intro a _ b _ hab
          exact Prod.ext (congrArg Sigma.fst hab) (congrArg (fun z ↦ z.2) hab)
        · intro z hz
          obtain ⟨ha, hu⟩ := Finset.mem_sigma.mp hz
          exact ⟨(z.1, z.2), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨ha, Finset.mem_univ _⟩, hu⟩, rfl⟩
      _ = _ := Finset.card_sigma _ _
  have hw' : 3 * (targets.card * Fintype.card Block * K) ≤
      8 * (Fintype.card State * good.card) := by
    convert hw using 1
    congr 2
    apply congrArg Finset.card
    ext az
    simp only [good, Isolated, Finset.mem_filter]
  refine ⟨w, hw'.trans ?_⟩
  apply Nat.mul_le_mul_left 8
  apply Nat.mul_le_mul_left (Fintype.card State)
  exact (Finset.card_le_card hsub).trans_eq hcard


end MME.DWZOwnerMass

theorem solution
    {State Edge Block X Y Z : Type*}
    [Fintype State] [Nonempty State] [DecidableEq State]
    [Fintype Edge] [DecidableEq Edge]
    [Fintype Block] [DecidableEq Block] [DecidableEq X] [DecidableEq Y]
    (targets ambient : Finset Edge) (events : Edge → Finset State)
    (x : Edge → X) (y : Edge → Y)
    (embed : Edge → Block → Z) (compatible : Z → Edge → Prop)
    (hsub : targets ⊆ ambient)
    (hself : ∀ a ∈ targets, ∀ z, compatible (embed a z) a)
    (K J p d c : ℕ) (hK : K = p * J)
    (hxyBudget : 4 * d ≤ p) (hzBudget : 8 * c ≤ p)
    (hsingle : ∀ a ∈ targets, (events a).card = K)
    (hx : ∀ a ∈ targets, (ambient.filter (fun b ↦ x b = x a)).card ≤ d)
    (hy : ∀ a ∈ targets, (ambient.filter (fun b ↦ y b = y a)).card ≤ d)
    (hzCard : ∀ a ∈ targets, ∀ z,
      (competitors targets embed compatible a z).card ≤ c)
    (hxyPair : ∀ a ∈ targets, ∀ b ∈ ambient,
      b ≠ a → (x b = x a ∨ y b = y a) →
        (events a ∩ events b).card ≤ J)
    (hzPair : ∀ a ∈ targets, ∀ z, ∀ b ∈ competitors targets embed compatible a z,
      (events a ∩ events b).card ≤ J) :
    ∃ w : State,
      (Set.InjOn x (selected targets ambient events x y w : Set Edge) ∧
        Set.InjOn y (selected targets ambient events x y w : Set Edge)) ∧
      (∀ a b : Edge, b ∈ selected targets ambient events x y w → ∀ u v : Block,
        u ∈ nonholes (selected targets ambient events x y w) embed compatible a →
        embed a u = embed b v → b = a) ∧
      3 * (targets.card * Fintype.card Block * K) ≤
        8 * (Fintype.card State *
          ∑ a ∈ selected targets ambient events x y w,
            (nonholes (selected targets ambient events x y w) embed compatible a).card) := by
  obtain ⟨w, hw⟩ := exists_selected_nonhole_mass targets ambient events x y embed compatible
    K J p d c hK hxyBudget hzBudget hsingle hx hy hzCard hxyPair hzPair
  refine ⟨w, selected_xy_injective targets ambient events x y hsub w, ?_, hw⟩
  intro a b hb u v hu heq
  apply nonhole_image_owner_unique (selected targets ambient events x y w)
    embed compatible ?_ a b hb u v hu heq
  intro a ha z
  exact hself a (selected_spec targets ambient events x y w a ha).1 z

