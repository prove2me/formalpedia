-- Prove2me | solution 1 for mme_dwz_joint_hash_ambient_xy_isolation_nonhole_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T08:09:24.931673+00:00
-- url     : https://prove2.me/submissions/720dcd18-9c4c-4819-a36c-6ac9120ad67b

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith

/-!
# One hash state with large total nonhole mass

This file uses only Mathlib. It does not assume a tensor realization or a
compatibility-count theorem. It combines the two kinds of deletions in ONE
probability space: ambient X/Y collisions and compatible Z competitors.
The output counts surviving (outer-copy, useful-block) incidences. It does
not make the generally unjustified assertion that every retained copy has
seven eighths of its blocks under one common hash state.
-/

open BigOperators

set_option autoImplicit false

namespace MME.DWZJoint

variable {State Edge Block : Type*}
variable [Fintype State] [DecidableEq State] [DecidableEq Edge]

/-- States retaining `a` but no member of its competitor set. -/
def goodStates (events : Edge → Finset State) (a : Edge)
    (competitors : Finset Edge) : Finset State :=
  events a \ competitors.biUnion (fun b ↦ events a ∩ events b)

omit [Fintype State] [DecidableEq Edge] in
theorem mem_goodStates_iff (events : Edge → Finset State) (a : Edge)
    (competitors : Finset Edge) (w : State) :
    w ∈ goodStates events a competitors ↔
      w ∈ events a ∧ ∀ b ∈ competitors, w ∉ events b := by
  classical
  simp only [goodStates, Finset.mem_sdiff, Finset.mem_biUnion,
    Finset.mem_inter]
  constructor
  · rintro ⟨ha, hbad⟩
    exact ⟨ha, fun b hb hbw ↦ hbad ⟨b, hb, ha, hbw⟩⟩
  · rintro ⟨ha, hgood⟩
    exact ⟨ha, fun ⟨b, hb, _, hbw⟩ ↦ hgood b hb hbw⟩

omit [Fintype State] [DecidableEq Edge] in
/-- Union-bound deletion, with no independence assumption. -/
theorem goodStates_card_bound (events : Edge → Finset State) (a : Edge)
    (competitors : Finset Edge) (J : ℕ)
    (hpairs : ∀ b ∈ competitors, (events a ∩ events b).card ≤ J) :
    (events a).card ≤
      (goodStates events a competitors).card + competitors.card * J := by
  classical
  have hbad :
      (competitors.biUnion (fun b ↦ events a ∩ events b)).card ≤
        competitors.card * J := by
    calc
      _ ≤ ∑ b ∈ competitors, (events a ∩ events b).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ competitors, J := Finset.sum_le_sum hpairs
      _ = _ := by simp
  exact (Finset.card_le_card_sdiff_add_card (s := events a)
    (t := competitors.biUnion (fun b ↦ events a ∩ events b))).trans
      (Nat.add_le_add_left hbad _)

/-- Double-count incidences, then choose a state of at least average mass. -/
theorem exists_state_at_least_average [Nonempty State]
    {Item : Type*} [DecidableEq Item]
    (items : Finset Item) (events : Item → Finset State) :
    ∃ w : State,
      (∑ a ∈ items, (events a).card) ≤
        Fintype.card State * (items.filter (fun a ↦ w ∈ events a)).card := by
  classical
  let mass : State → ℕ := fun w ↦
    (items.filter (fun a ↦ w ∈ events a)).card
  have hdouble : (∑ a ∈ items, (events a).card) = ∑ w : State, mass w := by
    have hcard (a : Item) : (events a).card =
        ∑ w : State, if w ∈ events a then 1 else 0 := by simp
    simp_rw [hcard]
    rw [Finset.sum_comm]
    simp [mass]
  obtain ⟨w, _, hw⟩ := Finset.exists_max_image
    (Finset.univ : Finset State) mass Finset.univ_nonempty
  refine ⟨w, ?_⟩
  rw [hdouble]
  calc
    _ ≤ ∑ _v : State, mass w := Finset.sum_le_sum hw
    _ = _ := by simp [mass]

/-- The shared hash state contains many nonhole incidences whenever each
target is retained in `K` states and each forbidden pair in at most `J`.
`xyCompetitors` must include competitors from the ambient same-marginal
family; `zCompetitors` must include only genuinely compatible competitors.
The proof pays for both deletions before choosing the single state.
-/
theorem exists_joint_nonhole_mass [Nonempty State]
    [Fintype Block] [DecidableEq Block]
    (targets : Finset Edge) (events : Edge → Finset State)
    (xyCompetitors : Edge → Finset Edge)
    (zCompetitors : Edge → Block → Finset Edge)
    (K J D C : ℕ)
    (hsingle : ∀ a ∈ targets, (events a).card = K)
    (hxyCard : ∀ a ∈ targets, (xyCompetitors a).card ≤ D)
    (hzCard : ∀ a ∈ targets, ∀ z, (zCompetitors a z).card ≤ C)
    (hxyPair : ∀ a ∈ targets, ∀ b ∈ xyCompetitors a,
      (events a ∩ events b).card ≤ J)
    (hzPair : ∀ a ∈ targets, ∀ z, ∀ b ∈ zCompetitors a z,
      (events a ∩ events b).card ≤ J) :
    ∃ w : State,
      targets.card * Fintype.card Block * K ≤
        Fintype.card State *
          ((targets.product Finset.univ).filter (fun az ↦
            w ∈ goodStates events az.1
              (xyCompetitors az.1 ∪ zCompetitors az.1 az.2))).card +
        targets.card * Fintype.card Block * ((D + C) * J) := by
  classical
  let items := targets.product (Finset.univ : Finset Block)
  let joint : Edge × Block → Finset State := fun az ↦
    goodStates events az.1 (xyCompetitors az.1 ∪ zCompetitors az.1 az.2)
  have heach (az : Edge × Block) (haz : az ∈ items) :
      K ≤ (joint az).card + (D + C) * J := by
    have ha : az.1 ∈ targets := (Finset.mem_product.mp haz).1
    have hpairs : ∀ b ∈ xyCompetitors az.1 ∪ zCompetitors az.1 az.2,
        (events az.1 ∩ events b).card ≤ J := by
      intro b hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact hxyPair az.1 ha b hb
      · exact hzPair az.1 ha az.2 b hb
    have hc : (xyCompetitors az.1 ∪ zCompetitors az.1 az.2).card ≤ D + C :=
      (Finset.card_union_le _ _).trans
        (Nat.add_le_add (hxyCard az.1 ha) (hzCard az.1 ha az.2))
    have hb := goodStates_card_bound events az.1
      (xyCompetitors az.1 ∪ zCompetitors az.1 az.2) J hpairs
    rw [hsingle az.1 ha] at hb
    exact hb.trans (Nat.add_le_add_left (Nat.mul_le_mul_right J hc) _)
  have hsum := Finset.sum_le_sum heach
  have hsum' : targets.card * Fintype.card Block * K ≤
      (∑ az ∈ items, (joint az).card) +
        targets.card * Fintype.card Block * ((D + C) * J) := by
    simpa [Finset.sum_add_distrib, items] using hsum
  obtain ⟨w, hw⟩ := exists_state_at_least_average items joint
  exact ⟨w, hsum'.trans (Nat.add_le_add_right hw _)⟩

/-- Competitors include every same-marginal ambient completion, not merely
the exact-profile target set. -/
def ambientXYCompetitors {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (ambient : Finset Edge) (x : Edge → X) (y : Edge → Y) (a : Edge) :
    Finset Edge :=
  ambient.filter (fun b ↦ b ≠ a ∧ (x b = x a ∨ y b = y a))

theorem ambientXYCompetitors_card_le {X Y : Type*}
    [DecidableEq X] [DecidableEq Y]
    (ambient : Finset Edge) (x : Edge → X) (y : Edge → Y)
    (a : Edge) (d : ℕ)
    (hx : (ambient.filter (fun b ↦ x b = x a)).card ≤ d)
    (hy : (ambient.filter (fun b ↦ y b = y a)).card ≤ d) :
    (ambientXYCompetitors ambient x y a).card ≤ 2 * d := by
  classical
  have hsub : ambientXYCompetitors ambient x y a ⊆
      (ambient.filter (fun b ↦ x b = x a)) ∪
        (ambient.filter (fun b ↦ y b = y a)) := by
    intro b hb
    rcases Finset.mem_filter.mp hb with ⟨hbA, _, hxy⟩
    rcases hxy with hx | hy
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hbA, hx⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hbA, hy⟩)
  calc
    _ ≤ ((ambient.filter (fun b ↦ x b = x a)) ∪
        (ambient.filter (fun b ↦ y b = y a))).card := Finset.card_le_card hsub
    _ ≤ (ambient.filter (fun b ↦ x b = x a)).card +
        (ambient.filter (fun b ↦ y b = y a)).card := Finset.card_union_le _ _
    _ ≤ d + d := Nat.add_le_add hx hy
    _ = 2 * d := by omega

omit [Fintype State] in
/-- Every counted incidence has an outer copy isolated against all retained
ambient X/Y competitors. -/
theorem goodStates_ambient_isolation {X Y : Type*}
    [DecidableEq X] [DecidableEq Y]
    (ambient : Finset Edge) (events : Edge → Finset State)
    (x : Edge → X) (y : Edge → Y) (a b : Edge)
    (zCompetitors : Finset Edge) (w : State)
    (hw : w ∈ goodStates events a
      (ambientXYCompetitors ambient x y a ∪ zCompetitors))
    (hb : b ∈ ambient) (hbRetained : w ∈ events b)
    (hshare : x b = x a ∨ y b = y a) : b = a := by
  classical
  by_contra hne
  have hcomp : b ∈ ambientXYCompetitors ambient x y a :=
    Finset.mem_filter.mpr ⟨hb, hne, hshare⟩
  exact ((mem_goodStates_iff events a _ w).mp hw).2 b
    (Finset.mem_union_left _ hcomp) hbRetained

/-- Concrete asymmetric-hash budgets leave three eighths of the original
incidence mass after BOTH ambient X/Y isolation and compatible-Z deletion.
Here `K = p*J` is the singleton/pair hash-fiber ratio. With the usual
`K = B*p^(N+1)` and `card State = p^(N+3)`, this is the lower bound
`3*card(targets)*card(Block)*B/(8*p^2)` on total nonhole incidences.
All competitors and both deletions use the SAME returned state.
-/
theorem exists_joint_nonhole_mass_three_eighths [Nonempty State]
    [Fintype Block] [DecidableEq Block]
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (targets ambient : Finset Edge) (events : Edge → Finset State)
    (x : Edge → X) (y : Edge → Y)
    (zCompetitors : Edge → Block → Finset Edge)
    (K J p d c : ℕ) (hK : K = p * J)
    (hxyBudget : 4 * d ≤ p) (hzBudget : 8 * c ≤ p)
    (hsingle : ∀ a ∈ targets, (events a).card = K)
    (hx : ∀ a ∈ targets, (ambient.filter (fun b ↦ x b = x a)).card ≤ d)
    (hy : ∀ a ∈ targets, (ambient.filter (fun b ↦ y b = y a)).card ≤ d)
    (hzCard : ∀ a ∈ targets, ∀ z, (zCompetitors a z).card ≤ c)
    (hxyPair : ∀ a ∈ targets,
      ∀ b ∈ ambientXYCompetitors ambient x y a,
        (events a ∩ events b).card ≤ J)
    (hzPair : ∀ a ∈ targets, ∀ z, ∀ b ∈ zCompetitors a z,
      (events a ∩ events b).card ≤ J) :
    ∃ w : State,
      3 * (targets.card * Fintype.card Block * K) ≤
        8 * (Fintype.card State *
          ((targets.product Finset.univ).filter (fun az ↦
            w ∈ goodStates events az.1
              (ambientXYCompetitors ambient x y az.1 ∪
                zCompetitors az.1 az.2))).card) := by
  classical
  have hxyCard : ∀ a ∈ targets,
      (ambientXYCompetitors ambient x y a).card ≤ 2 * d := by
    intro a ha
    exact ambientXYCompetitors_card_le ambient x y a d (hx a ha) (hy a ha)
  obtain ⟨w, hw⟩ := exists_joint_nonhole_mass targets events
    (ambientXYCompetitors ambient x y) zCompetitors
    K J (2 * d) c hsingle hxyCard hzCard hxyPair hzPair
  refine ⟨w, ?_⟩
  have hb : 8 * (2 * d + c) ≤ 5 * p := by omega
  have hbJ := Nat.mul_le_mul_right J hb
  have hbTotal := Nat.mul_le_mul_left
    (targets.card * Fintype.card Block) hbJ
  rw [hK] at hw ⊢
  nlinarith

end MME.DWZJoint



set_option warningAsError true

theorem solution
    {State Edge Block X Y : Type*}
    [Fintype State] [Nonempty State] [DecidableEq State]
    [Fintype Edge] [DecidableEq Edge]
    [Fintype Block] [DecidableEq Block] [DecidableEq X] [DecidableEq Y]
    (targets ambient : Finset Edge) (events : Edge → Finset State)
    (x : Edge → X) (y : Edge → Y)
    (zCompetitors : Edge → Block → Finset Edge)
    (K J p d c : ℕ) (hK : K = p * J)
    (hxyBudget : 4 * d ≤ p) (hzBudget : 8 * c ≤ p)
    (hsingle : ∀ a ∈ targets, (events a).card = K)
    (hx : ∀ a ∈ targets, (ambient.filter (fun b ↦ x b = x a)).card ≤ d)
    (hy : ∀ a ∈ targets, (ambient.filter (fun b ↦ y b = y a)).card ≤ d)
    (hzCard : ∀ a ∈ targets, ∀ z, (zCompetitors a z).card ≤ c)
    (hxyPair : ∀ a ∈ targets, ∀ b ∈ ambient,
      b ≠ a → (x b = x a ∨ y b = y a) →
        (events a ∩ events b).card ≤ J)
    (hzPair : ∀ a ∈ targets, ∀ z, ∀ b ∈ zCompetitors a z,
      (events a ∩ events b).card ≤ J) :
    ∃ w : State,
      3 * (targets.card * Fintype.card Block * K) ≤
        8 * (Fintype.card State *
          ((targets.product Finset.univ).filter (fun az ↦
            w ∈ events az.1 ∧
              (∀ b ∈ ambient, w ∈ events b →
                (x b = x az.1 ∨ y b = y az.1) → b = az.1) ∧
              ∀ b ∈ zCompetitors az.1 az.2, w ∉ events b)).card) := by
  classical
  have hxyPair' : ∀ a ∈ targets,
      ∀ b ∈ MME.DWZJoint.ambientXYCompetitors ambient x y a,
        (events a ∩ events b).card ≤ J := by
    intro a ha b hb
    rcases Finset.mem_filter.mp hb with ⟨hbA, hne, hshare⟩
    exact hxyPair a ha b hbA hne hshare
  obtain ⟨w, hw⟩ := MME.DWZJoint.exists_joint_nonhole_mass_three_eighths
    targets ambient events x y zCompetitors K J p d c hK hxyBudget
    hzBudget hsingle hx hy hzCard hxyPair' hzPair
  refine ⟨w, ?_⟩
  have hfilter :
      ((targets.product Finset.univ).filter (fun az ↦
        w ∈ MME.DWZJoint.goodStates events az.1
          (MME.DWZJoint.ambientXYCompetitors ambient x y az.1 ∪
            zCompetitors az.1 az.2))) =
      ((targets.product Finset.univ).filter (fun az ↦
        w ∈ events az.1 ∧
          (∀ b ∈ ambient, w ∈ events b →
            (x b = x az.1 ∨ y b = y az.1) → b = az.1) ∧
          ∀ b ∈ zCompetitors az.1 az.2, w ∉ events b)) := by
    apply Finset.filter_congr
    intro az _
    constructor
    · intro h
      have hg := (MME.DWZJoint.mem_goodStates_iff events az.1 _ w).mp h
      refine ⟨hg.1, ?_, ?_⟩
      · intro b hb hbRetained hshare
        exact MME.DWZJoint.goodStates_ambient_isolation
          ambient events x y az.1 b (zCompetitors az.1 az.2) w
          h hb hbRetained hshare
      · intro b hb
        exact hg.2 b (Finset.mem_union_right _ hb)
    · rintro ⟨ha, hxy, hz⟩
      apply (MME.DWZJoint.mem_goodStates_iff events az.1 _ w).mpr
      refine ⟨ha, ?_⟩
      intro b hb
      rcases Finset.mem_union.mp hb with hb | hb
      · rcases Finset.mem_filter.mp hb with ⟨hbA, hne, hshare⟩
        intro hbRetained
        exact hne (hxy b hbA hbRetained hshare)
      · exact hz b hb
  rw [hfilter] at hw
  exact hw

#print axioms solution
