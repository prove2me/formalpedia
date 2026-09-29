-- Prove2me | solution 1 for KServer.ckPotK_anchor_at_request_ge_three
-- status  : ACCEPTED   (disprove)
-- author  : @Gabewhigham
-- created : 2026-09-09T08:04:46.442986+00:00
-- url     : https://prove2.me/submissions/304ed336-f41d-43cf-8a3e-aa3290682552

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential_k

/-!
# A counterexample to the anchor property of the Coester–Koutsoupias potential
-/

namespace CEK

open KServer

/-! ## Part 1 : general facts about the work function -/

section General

variable {k : ℕ} {M : Type} [MetricSpace M]

/-- The set of costs whose infimum defines `workFn`. -/
def costSet (C₀ : Config k M) (σ : List M) (X : Config k M) : Set ℝ :=
  {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
    c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X}

theorem workFn_eq_sInf (C₀ : Config k M) (σ : List M) (X : Config k M) :
    workFn C₀ σ X = sInf (costSet C₀ σ X) := rfl

theorem moveCost_nonneg (C C' : Config k M) : 0 ≤ moveCost C C' :=
  Finset.sum_nonneg fun _ _ => dist_nonneg

theorem costSet_bddBelow (C₀ : Config k M) (σ : List M) (X : Config k M) :
    BddBelow (costSet C₀ σ X) := by
  refine ⟨0, ?_⟩
  rintro c ⟨S, -, rfl⟩
  have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun _ _ => moveCost_nonneg _ _
  have h2 := moveCost_nonneg (S σ.length) X
  linarith

/-- A schedule serving any request sequence exists as soon as there is at least one server. -/
theorem exists_serves (hk : 0 < k) (C₀ : Config k M) (σ : List M) :
    ∃ S : ℕ → Config k M, ServesFrom C₀ σ S := by
  classical
  refine ⟨fun j => if j = 0 then C₀ else
      Function.update C₀ ⟨0, hk⟩ (σ.getD (j - 1) (C₀ ⟨0, hk⟩)), by simp, ?_⟩
  intro j
  refine ⟨⟨0, hk⟩, ?_⟩
  have h1 : ((j : ℕ) + 1) ≠ 0 := by omega
  simp only [h1, if_false, Nat.add_sub_cancel, Function.update_self]
  rw [List.getD_eq_getElem _ _ j.isLt]
  simp

theorem costSet_nonempty (hk : 0 < k) (C₀ : Config k M) (σ : List M) (X : Config k M) :
    (costSet C₀ σ X).Nonempty := by
  obtain ⟨S, hS⟩ := exists_serves hk C₀ σ
  exact ⟨_, S, hS, rfl⟩

theorem workFn_le_of_mem {C₀ : Config k M} {σ : List M} {X : Config k M} {c : ℝ}
    (hc : c ∈ costSet C₀ σ X) : workFn C₀ σ X ≤ c :=
  csInf_le (costSet_bddBelow _ _ _) hc

theorem le_workFn (hk : 0 < k) {C₀ : Config k M} {σ : List M} {X : Config k M} {b : ℝ}
    (h : ∀ c ∈ costSet C₀ σ X, b ≤ c) : b ≤ workFn C₀ σ X :=
  le_csInf (costSet_nonempty hk C₀ σ X) h

/-- The work function of the empty request sequence is the moving cost. -/
theorem workFn_nil (C₀ X : Config k M) : workFn C₀ [] X = moveCost C₀ X := by
  have hset : costSet C₀ [] X = {moveCost C₀ X} := by
    ext c
    constructor
    · rintro ⟨S, ⟨h0, -⟩, rfl⟩
      simp [h0]
    · rintro rfl
      exact ⟨fun _ => C₀, ⟨rfl, by intro j; exact absurd j.isLt (by simp)⟩, by simp⟩
  rw [workFn_eq_sInf, hset, csInf_singleton]

variable [Fintype M] [DecidableEq M]

/-- Configurations in which some server sits on `q`. -/
def serving (q : M) : Finset (Config k M) :=
  Finset.univ.filter (fun Y : Config k M => ∃ i, Y i = q)

theorem serving_nonempty (hk : 0 < k) (q : M) : (serving (k := k) q).Nonempty := by
  refine ⟨fun _ => q, ?_⟩
  simp only [serving, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨⟨0, hk⟩, trivial⟩

theorem mem_serving {q : M} {Y : Config k M} : Y ∈ serving q ↔ ∃ i, Y i = q := by
  simp [serving]

/-- Extending a schedule for `σ` by one final configuration `Y` containing `q`. -/
theorem workFn_snoc_le (hk : 0 < k) (C₀ : Config k M) (σ : List M) (q : M) (X Y : Config k M)
    (hY : ∃ i, Y i = q) :
    workFn C₀ (σ ++ [q]) X ≤ workFn C₀ σ Y + moveCost Y X := by
  classical
  obtain ⟨i₀, hi₀⟩ := hY
  have key : ∀ c ∈ costSet C₀ σ Y, workFn C₀ (σ ++ [q]) X ≤ c + moveCost Y X := by
    rintro c ⟨S, ⟨hS0, hS⟩, rfl⟩
    set T : ℕ → Config k M := fun j => if j ≤ σ.length then S j else Y with hT
    have hTle : ∀ j, j ≤ σ.length → T j = S j := by
      intro j hj; simp only [hT]; rw [if_pos hj]
    have hTgt : ∀ j, ¬ j ≤ σ.length → T j = Y := by
      intro j hj; simp only [hT]; rw [if_neg hj]
    refine workFn_le_of_mem ⟨T, ⟨?_, ?_⟩, ?_⟩
    · rw [hTle 0 (Nat.zero_le _)]; exact hS0
    · intro j
      have hjlt : (j : ℕ) < σ.length + 1 := by have := j.isLt; simpa using this
      rcases Nat.lt_or_ge (j : ℕ) σ.length with hj | hj
      · obtain ⟨i, hi⟩ := hS ⟨(j : ℕ), hj⟩
        refine ⟨i, ?_⟩
        rw [hTle _ (by omega), hi]
        simp [List.get_eq_getElem, List.getElem_append, hj]
      · have hj' : (j : ℕ) = σ.length := by omega
        refine ⟨i₀, ?_⟩
        rw [hTgt _ (by omega), hi₀]
        simp [List.get_eq_getElem, List.getElem_append, hj']
    · have hlen : (σ ++ [q]).length = σ.length + 1 := by simp
      rw [hlen, Finset.sum_range_succ]
      have h1 : ∀ j ∈ Finset.range σ.length, moveCost (T j) (T (j+1)) = moveCost (S j) (S (j+1)) := by
        intro j hj
        simp only [Finset.mem_range] at hj
        rw [hTle _ (by omega), hTle _ (by omega)]
      rw [Finset.sum_congr rfl h1, hTle _ (le_refl _), hTgt _ (by omega)]
  have h2 : workFn C₀ (σ ++ [q]) X - moveCost Y X ≤ workFn C₀ σ Y :=
    le_csInf (costSet_nonempty hk C₀ σ Y) (fun c hc => by have := key c hc; linarith)
  linarith

/-- One step of the work function recursion. -/
theorem workFn_snoc (hk : 0 < k) (C₀ : Config k M) (σ : List M) (q : M) (X : Config k M) :
    workFn C₀ (σ ++ [q]) X =
      (serving q).inf' (serving_nonempty hk q) (fun Y => workFn C₀ σ Y + moveCost Y X) := by
  classical
  apply le_antisymm
  · exact Finset.le_inf' _ _ (fun Y hY => workFn_snoc_le hk C₀ σ q X Y (mem_serving.mp hY))
  · apply le_workFn hk
    rintro c ⟨S, ⟨hS0, hS⟩, rfl⟩
    have hlen : (σ ++ [q]).length = σ.length + 1 := by simp
    have hlast : ∃ i, S (σ.length + 1) i = q := by
      obtain ⟨i, hi⟩ := hS ⟨σ.length, by rw [hlen]; omega⟩
      exact ⟨i, by rw [hi]; simp [List.get_eq_getElem, List.getElem_append]⟩
    have hsub : workFn C₀ σ (S (σ.length+1))
        ≤ (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
            + moveCost (S σ.length) (S (σ.length+1)) := by
      refine workFn_le_of_mem ⟨S, ⟨hS0, ?_⟩, rfl⟩
      intro j
      have hj : (j : ℕ) < σ.length := j.isLt
      obtain ⟨i, hi⟩ := hS ⟨(j : ℕ), by rw [hlen]; omega⟩
      exact ⟨i, by rw [hi]; simp [List.get_eq_getElem, List.getElem_append, hj]⟩
    calc (serving q).inf' (serving_nonempty hk q) (fun Y => workFn C₀ σ Y + moveCost Y X)
        ≤ workFn C₀ σ (S (σ.length+1)) + moveCost (S (σ.length+1)) X :=
          Finset.inf'_le _ (mem_serving.mpr hlast)
      _ ≤ ((∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
            + moveCost (S σ.length) (S (σ.length+1))) + moveCost (S (σ.length+1)) X := by
            linarith
      _ = (∑ j ∈ Finset.range (σ ++ [q]).length, moveCost (S j) (S (j + 1)))
            + moveCost (S (σ ++ [q]).length) X := by
            rw [hlen, Finset.sum_range_succ]

end General

/-! ## Part 2 : the counterexample metric space

`Pt` is a seven point subset of the circle of circumference `32`, namely the points
`3, 9, 13, 14, 20, 24, 29`, with the induced (integer) circle metric. -/

inductive Pt | p0 | p1 | p2 | p3 | p4 | p5 | p6
  deriving DecidableEq, Fintype

def dm : Pt → Pt → ℤ
  | Pt.p0, Pt.p0 => 0
  | Pt.p0, Pt.p1 => 6
  | Pt.p0, Pt.p2 => 10
  | Pt.p0, Pt.p3 => 11
  | Pt.p0, Pt.p4 => 15
  | Pt.p0, Pt.p5 => 11
  | Pt.p0, Pt.p6 => 6
  | Pt.p1, Pt.p0 => 6
  | Pt.p1, Pt.p1 => 0
  | Pt.p1, Pt.p2 => 4
  | Pt.p1, Pt.p3 => 5
  | Pt.p1, Pt.p4 => 11
  | Pt.p1, Pt.p5 => 15
  | Pt.p1, Pt.p6 => 12
  | Pt.p2, Pt.p0 => 10
  | Pt.p2, Pt.p1 => 4
  | Pt.p2, Pt.p2 => 0
  | Pt.p2, Pt.p3 => 1
  | Pt.p2, Pt.p4 => 7
  | Pt.p2, Pt.p5 => 11
  | Pt.p2, Pt.p6 => 16
  | Pt.p3, Pt.p0 => 11
  | Pt.p3, Pt.p1 => 5
  | Pt.p3, Pt.p2 => 1
  | Pt.p3, Pt.p3 => 0
  | Pt.p3, Pt.p4 => 6
  | Pt.p3, Pt.p5 => 10
  | Pt.p3, Pt.p6 => 15
  | Pt.p4, Pt.p0 => 15
  | Pt.p4, Pt.p1 => 11
  | Pt.p4, Pt.p2 => 7
  | Pt.p4, Pt.p3 => 6
  | Pt.p4, Pt.p4 => 0
  | Pt.p4, Pt.p5 => 4
  | Pt.p4, Pt.p6 => 9
  | Pt.p5, Pt.p0 => 11
  | Pt.p5, Pt.p1 => 15
  | Pt.p5, Pt.p2 => 11
  | Pt.p5, Pt.p3 => 10
  | Pt.p5, Pt.p4 => 4
  | Pt.p5, Pt.p5 => 0
  | Pt.p5, Pt.p6 => 5
  | Pt.p6, Pt.p0 => 6
  | Pt.p6, Pt.p1 => 12
  | Pt.p6, Pt.p2 => 16
  | Pt.p6, Pt.p3 => 15
  | Pt.p6, Pt.p4 => 9
  | Pt.p6, Pt.p5 => 5
  | Pt.p6, Pt.p6 => 0


theorem dm_self (x : Pt) : dm x x = 0 := by revert x; decide
theorem dm_comm (x y : Pt) : dm x y = dm y x := by revert x y; decide
theorem dm_tri (x y z : Pt) : dm x z ≤ dm x y + dm y z := by revert x y z; decide
theorem dm_pos (x y : Pt) (h : x ≠ y) : 0 < dm x y := by revert x y; decide
theorem dm_le (x y : Pt) : dm x y ≤ 16 := by revert x y; decide

noncomputable instance ptMS : MetricSpace Pt where
  dist x y := ((dm x y : ℤ) : ℝ)
  dist_self x := by simp [dm_self x]
  dist_comm x y := by rw [dm_comm]
  dist_triangle x y z := by exact_mod_cast dm_tri x y z
  eq_of_dist_eq_zero := by
    intro x y h
    by_contra hne
    have h1 := dm_pos x y hne
    have h2 : (dm x y : ℤ) = 0 := by exact_mod_cast h
    omega

theorem dist_pt (x y : Pt) : dist x y = ((dm x y : ℤ) : ℝ) := rfl

theorem hD0 : (0:ℝ) < 16 := by norm_num

theorem hDle : ∀ x y : Pt, dist x y ≤ (16:ℝ) := by
  intro x y
  rw [dist_pt]
  exact_mod_cast dm_le x y

/-- The antipodal extension of `Pt` at scale `Δ = 16`. -/
abbrev NN := Pt ⊕ Pt

noncomputable abbrev nnMS : MetricSpace NN := antipodalExtension Pt 16 hD0 hDle

attribute [local instance] nnMS

/-- The integer distance table of the antipodal extension. -/
def DZ : NN → NN → ℤ
  | Sum.inl x, Sum.inl y => dm x y
  | Sum.inr x, Sum.inr y => dm x y
  | Sum.inl x, Sum.inr y => 32 - dm x y
  | Sum.inr x, Sum.inl y => 32 - dm x y

theorem dist_nn (p q : NN) : dist p q = ((DZ p q : ℤ) : ℝ) := by
  rcases p with x | x <;> rcases q with y | y <;>
    · show antiD (16:ℝ) _ _ = _
      simp only [antiD, DZ, dist_pt]
      try (push_cast; ring)

theorem DZ_self (p : NN) : DZ p p = 0 := by revert p; decide
theorem DZ_tri (p q r : NN) : DZ p r ≤ DZ p q + DZ q r := by revert p q r; decide
theorem DZ_le (p q : NN) : DZ p q ≤ 32 := by revert p q; decide

/-! ## Part 3 : configurations as triples, and the support certificate -/

abbrev Cfg := Config 3 NN
abbrev Tri := NN × NN × NN
/-- An entry of a certificate: a configuration, its work function value, and a witness
configuration used for the upper bound. -/
abbrev Ent := Tri × ℤ × Tri

def L0 : List Ent :=
  [(((.inl Pt.p0), (.inl Pt.p4), (.inl Pt.p6)), 0, ((.inl Pt.p0), (.inl Pt.p4), (.inl Pt.p6)))]

def L1 : List Ent :=
  [(((.inl Pt.p0), (.inl Pt.p4), (.inl Pt.p5)), 5, ((.inl Pt.p0), (.inl Pt.p4), (.inl Pt.p5))),
   (((.inl Pt.p0), (.inl Pt.p5), (.inl Pt.p6)), 4, ((.inl Pt.p0), (.inl Pt.p5), (.inl Pt.p6))),
   (((.inl Pt.p5), (.inl Pt.p4), (.inl Pt.p6)), 11, ((.inl Pt.p5), (.inl Pt.p4), (.inl Pt.p6)))]

def L2 : List Ent :=
  [(((.inl Pt.p0), (.inl Pt.p4), (.inl Pt.p5)), 5, ((.inl Pt.p0), (.inl Pt.p4), (.inl Pt.p5))),
   (((.inl Pt.p0), (.inl Pt.p4), (.inl Pt.p6)), 8, ((.inl Pt.p0), (.inl Pt.p4), (.inl Pt.p6))),
   (((.inl Pt.p5), (.inl Pt.p4), (.inl Pt.p6)), 11, ((.inl Pt.p5), (.inl Pt.p4), (.inl Pt.p6)))]

def L3 : List Ent :=
  [(((.inl Pt.p0), (.inl Pt.p1), (.inl Pt.p5)), 16, ((.inl Pt.p0), (.inl Pt.p1), (.inl Pt.p5))),
   (((.inl Pt.p0), (.inl Pt.p1), (.inl Pt.p6)), 19, ((.inl Pt.p0), (.inl Pt.p1), (.inl Pt.p6))),
   (((.inl Pt.p0), (.inl Pt.p4), (.inl Pt.p1)), 20, ((.inl Pt.p0), (.inl Pt.p4), (.inl Pt.p1))),
   (((.inl Pt.p1), (.inl Pt.p4), (.inl Pt.p5)), 11, ((.inl Pt.p1), (.inl Pt.p4), (.inl Pt.p5))),
   (((.inl Pt.p1), (.inl Pt.p4), (.inl Pt.p6)), 14, ((.inl Pt.p1), (.inl Pt.p4), (.inl Pt.p6))),
   (((.inl Pt.p5), (.inl Pt.p1), (.inl Pt.p6)), 22, ((.inl Pt.p5), (.inl Pt.p1), (.inl Pt.p6))),
   (((.inl Pt.p5), (.inl Pt.p4), (.inl Pt.p1)), 23, ((.inl Pt.p5), (.inl Pt.p4), (.inl Pt.p1)))]

def L4 : List Ent :=
  [(((.inl Pt.p0), (.inl Pt.p1), (.inl Pt.p2)), 27, ((.inl Pt.p0), (.inl Pt.p1), (.inl Pt.p2))),
   (((.inl Pt.p0), (.inl Pt.p2), (.inl Pt.p1)), 27, ((.inl Pt.p0), (.inl Pt.p2), (.inl Pt.p1))),
   (((.inl Pt.p0), (.inl Pt.p2), (.inl Pt.p5)), 20, ((.inl Pt.p0), (.inl Pt.p2), (.inl Pt.p5))),
   (((.inl Pt.p0), (.inl Pt.p2), (.inl Pt.p6)), 23, ((.inl Pt.p0), (.inl Pt.p2), (.inl Pt.p6))),
   (((.inl Pt.p0), (.inl Pt.p4), (.inl Pt.p2)), 24, ((.inl Pt.p0), (.inl Pt.p4), (.inl Pt.p2))),
   (((.inl Pt.p1), (.inl Pt.p2), (.inl Pt.p5)), 18, ((.inl Pt.p1), (.inl Pt.p2), (.inl Pt.p5))),
   (((.inl Pt.p1), (.inl Pt.p2), (.inl Pt.p6)), 21, ((.inl Pt.p1), (.inl Pt.p2), (.inl Pt.p6))),
   (((.inl Pt.p1), (.inl Pt.p4), (.inl Pt.p2)), 22, ((.inl Pt.p1), (.inl Pt.p4), (.inl Pt.p2))),
   (((.inl Pt.p2), (.inl Pt.p4), (.inl Pt.p5)), 15, ((.inl Pt.p2), (.inl Pt.p4), (.inl Pt.p5))),
   (((.inl Pt.p2), (.inl Pt.p4), (.inl Pt.p6)), 18, ((.inl Pt.p2), (.inl Pt.p4), (.inl Pt.p6))),
   (((.inl Pt.p5), (.inl Pt.p2), (.inl Pt.p1)), 30, ((.inl Pt.p5), (.inl Pt.p2), (.inl Pt.p1))),
   (((.inl Pt.p5), (.inl Pt.p2), (.inl Pt.p6)), 26, ((.inl Pt.p5), (.inl Pt.p2), (.inl Pt.p6))),
   (((.inl Pt.p5), (.inl Pt.p4), (.inl Pt.p2)), 27, ((.inl Pt.p5), (.inl Pt.p4), (.inl Pt.p2)))]

def L5 : List Ent :=
  [(((.inl Pt.p0), (.inl Pt.p1), (.inl Pt.p3)), 28, ((.inl Pt.p0), (.inl Pt.p1), (.inl Pt.p3))),
   (((.inl Pt.p0), (.inl Pt.p2), (.inl Pt.p3)), 30, ((.inl Pt.p0), (.inl Pt.p2), (.inl Pt.p3))),
   (((.inl Pt.p0), (.inl Pt.p3), (.inl Pt.p1)), 28, ((.inl Pt.p0), (.inl Pt.p3), (.inl Pt.p1))),
   (((.inl Pt.p0), (.inl Pt.p3), (.inl Pt.p2)), 30, ((.inl Pt.p0), (.inl Pt.p3), (.inl Pt.p2))),
   (((.inl Pt.p0), (.inl Pt.p3), (.inl Pt.p5)), 21, ((.inl Pt.p0), (.inl Pt.p3), (.inl Pt.p5))),
   (((.inl Pt.p0), (.inl Pt.p3), (.inl Pt.p6)), 24, ((.inl Pt.p0), (.inl Pt.p3), (.inl Pt.p6))),
   (((.inl Pt.p0), (.inl Pt.p4), (.inl Pt.p3)), 25, ((.inl Pt.p0), (.inl Pt.p4), (.inl Pt.p3))),
   (((.inl Pt.p1), (.inl Pt.p2), (.inl Pt.p3)), 28, ((.inl Pt.p1), (.inl Pt.p2), (.inl Pt.p3))),
   (((.inl Pt.p1), (.inl Pt.p3), (.inl Pt.p2)), 28, ((.inl Pt.p1), (.inl Pt.p3), (.inl Pt.p2))),
   (((.inl Pt.p1), (.inl Pt.p3), (.inl Pt.p5)), 19, ((.inl Pt.p1), (.inl Pt.p3), (.inl Pt.p5))),
   (((.inl Pt.p1), (.inl Pt.p3), (.inl Pt.p6)), 22, ((.inl Pt.p1), (.inl Pt.p3), (.inl Pt.p6))),
   (((.inl Pt.p1), (.inl Pt.p4), (.inl Pt.p3)), 23, ((.inl Pt.p1), (.inl Pt.p4), (.inl Pt.p3))),
   (((.inl Pt.p2), (.inl Pt.p3), (.inl Pt.p5)), 21, ((.inl Pt.p2), (.inl Pt.p3), (.inl Pt.p5))),
   (((.inl Pt.p2), (.inl Pt.p3), (.inl Pt.p6)), 24, ((.inl Pt.p2), (.inl Pt.p3), (.inl Pt.p6))),
   (((.inl Pt.p2), (.inl Pt.p4), (.inl Pt.p3)), 25, ((.inl Pt.p2), (.inl Pt.p4), (.inl Pt.p3))),
   (((.inl Pt.p3), (.inl Pt.p4), (.inl Pt.p5)), 16, ((.inl Pt.p3), (.inl Pt.p4), (.inl Pt.p5))),
   (((.inl Pt.p3), (.inl Pt.p4), (.inl Pt.p6)), 19, ((.inl Pt.p3), (.inl Pt.p4), (.inl Pt.p6))),
   (((.inl Pt.p5), (.inl Pt.p3), (.inl Pt.p1)), 31, ((.inl Pt.p5), (.inl Pt.p3), (.inl Pt.p1))),
   (((.inl Pt.p5), (.inl Pt.p3), (.inl Pt.p2)), 33, ((.inl Pt.p5), (.inl Pt.p3), (.inl Pt.p2))),
   (((.inl Pt.p5), (.inl Pt.p3), (.inl Pt.p6)), 27, ((.inl Pt.p5), (.inl Pt.p3), (.inl Pt.p6))),
   (((.inl Pt.p5), (.inl Pt.p4), (.inl Pt.p3)), 28, ((.inl Pt.p5), (.inl Pt.p4), (.inl Pt.p3)))]

def B3 : Pt → ℤ
  | Pt.p0 => 54
  | Pt.p1 => 54
  | Pt.p2 => 60
  | Pt.p3 => 62
  | Pt.p4 => 64
  | Pt.p5 => 66
  | Pt.p6 => 64

def B12 : Pt → Pt → ℤ
  | Pt.p0, Pt.p0 => 72
  | Pt.p0, Pt.p1 => 68
  | Pt.p0, Pt.p2 => 72
  | Pt.p0, Pt.p3 => 74
  | Pt.p0, Pt.p4 => 62
  | Pt.p0, Pt.p5 => 54
  | Pt.p0, Pt.p6 => 60
  | Pt.p1, Pt.p0 => 66
  | Pt.p1, Pt.p1 => 68
  | Pt.p1, Pt.p2 => 66
  | Pt.p1, Pt.p3 => 68
  | Pt.p1, Pt.p4 => 56
  | Pt.p1, Pt.p5 => 56
  | Pt.p1, Pt.p6 => 62
  | Pt.p2, Pt.p0 => 70
  | Pt.p2, Pt.p1 => 66
  | Pt.p2, Pt.p2 => 72
  | Pt.p2, Pt.p3 => 72
  | Pt.p2, Pt.p4 => 60
  | Pt.p2, Pt.p5 => 60
  | Pt.p2, Pt.p6 => 68
  | Pt.p3, Pt.p0 => 72
  | Pt.p3, Pt.p1 => 68
  | Pt.p3, Pt.p2 => 72
  | Pt.p3, Pt.p3 => 74
  | Pt.p3, Pt.p4 => 62
  | Pt.p3, Pt.p5 => 62
  | Pt.p3, Pt.p6 => 70
  | Pt.p4, Pt.p0 => 72
  | Pt.p4, Pt.p1 => 68
  | Pt.p4, Pt.p2 => 72
  | Pt.p4, Pt.p3 => 74
  | Pt.p4, Pt.p4 => 62
  | Pt.p4, Pt.p5 => 54
  | Pt.p4, Pt.p6 => 60
  | Pt.p5, Pt.p0 => 66
  | Pt.p5, Pt.p1 => 68
  | Pt.p5, Pt.p2 => 66
  | Pt.p5, Pt.p3 => 68
  | Pt.p5, Pt.p4 => 56
  | Pt.p5, Pt.p5 => 56
  | Pt.p5, Pt.p6 => 62
  | Pt.p6, Pt.p0 => 70
  | Pt.p6, Pt.p1 => 66
  | Pt.p6, Pt.p2 => 72
  | Pt.p6, Pt.p3 => 72
  | Pt.p6, Pt.p4 => 60
  | Pt.p6, Pt.p5 => 60
  | Pt.p6, Pt.p6 => 68

def B4 : ℤ := 94

def toCfg (t : Tri) : Cfg := ![t.1, t.2.1, t.2.2]
def ofCfg (X : Cfg) : Tri := (X 0, X 1, X 2)

theorem toCfg_ofCfg (X : Cfg) : toCfg (ofCfg X) = X := by
  funext i; fin_cases i <;> rfl

theorem ofCfg_toCfg (t : Tri) : ofCfg (toCfg t) = t := rfl

def MCz (s t : Tri) : ℤ := DZ s.1 t.1 + DZ s.2.1 t.2.1 + DZ s.2.2 t.2.2

theorem moveCost_eq (X Y : Cfg) : moveCost X Y = ((MCz (ofCfg X) (ofCfg Y) : ℤ) : ℝ) := by
  simp only [moveCost, Fin.sum_univ_three, MCz, ofCfg, dist_nn]
  push_cast
  ring

theorem MCz_tri (a b c : Tri) : MCz a c ≤ MCz a b + MCz b c := by
  have h1 := DZ_tri a.1 b.1 c.1
  have h2 := DZ_tri a.2.1 b.2.1 c.2.1
  have h3 := DZ_tri a.2.2 b.2.2 c.2.2
  simp only [MCz]; omega

theorem MCz_le (a b : Tri) : MCz a b ≤ 96 := by
  have h1 := DZ_le a.1 b.1
  have h2 := DZ_le a.2.1 b.2.1
  have h3 := DZ_le a.2.2 b.2.2
  simp only [MCz]; omega

/-- Minimum of a list of integers (with a large default). -/
def minList (l : List ℤ) : ℤ := l.foldr min 1000000

theorem minList_le {l : List ℤ} {x : ℤ} (hx : x ∈ l) : minList l ≤ x := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
      simp only [minList, List.foldr_cons] at *
      rcases List.mem_cons.mp hx with rfl | h
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih h)

theorem minList_cases (l : List ℤ) : minList l = 1000000 ∨ ∃ x ∈ l, minList l = x := by
  induction l with
  | nil => exact Or.inl rfl
  | cons a l ih =>
      simp only [minList, List.foldr_cons] at *
      rcases min_cases a (l.foldr min 1000000) with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inr ⟨a, List.mem_cons_self .., h1⟩
      · rcases ih with h | ⟨x, hx, h⟩
        · exact Or.inl (by rw [h1]; exact h)
        · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, by rw [h1]; exact h⟩

def valAt (t : Tri) (e : Ent) : ℤ := e.2.1 + MCz e.1 t

/-- The lower bound function attached to a certificate. -/
def PsiZ (L : List Ent) (t : Tri) : ℤ := minList (L.map (valAt t))

theorem PsiZ_le {L : List Ent} {e : Ent} (he : e ∈ L) (t : Tri) : PsiZ L t ≤ valAt t e :=
  minList_le (List.mem_map_of_mem he)

theorem PsiZ_att {L : List Ent} (hL : ∃ e ∈ L, e.2.1 ≤ 1000) (t : Tri) :
    ∃ e ∈ L, PsiZ L t = valAt t e := by
  obtain ⟨e₀, h0, hv⟩ := hL
  rcases minList_cases (L.map (valAt t)) with h | ⟨x, hx, h⟩
  · exfalso
    have h1 := PsiZ_le h0 t
    have h2 : valAt t e₀ ≤ 1000 + 96 := by
      have := MCz_le e₀.1 t
      simp only [valAt]; omega
    simp only [PsiZ, h] at h1
    omega
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact ⟨e, he, h⟩

theorem PsiZ_lip {L : List Ent} (hL : ∃ e ∈ L, e.2.1 ≤ 1000) (s t : Tri) :
    PsiZ L t ≤ PsiZ L s + MCz s t := by
  obtain ⟨e, he, heq⟩ := PsiZ_att hL s
  have h1 := PsiZ_le he t
  have h2 : valAt t e ≤ valAt s e + MCz s t := by
    have := MCz_tri e.1 s t
    simp only [valAt]; omega
  omega

/-- Replace the `i`-th coordinate of a triple. -/
def triUpd (t : Tri) (i : Fin 3) (q : NN) : Tri :=
  if i = 0 then (q, t.2.1, t.2.2) else if i = 1 then (t.1, q, t.2.2) else (t.1, t.2.1, q)

theorem MCz_split (s : Tri) (i : Fin 3) (Y : Cfg) :
    MCz s (ofCfg Y) = DZ (toCfg s i) (Y i) + MCz (triUpd s i (Y i)) (ofCfg Y) := by
  have h : i = 0 ∨ i = 1 ∨ i = 2 := by
    obtain ⟨j, hj⟩ := i
    interval_cases j
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  rcases h with rfl | rfl | rfl <;>
    simp only [MCz, triUpd, toCfg, ofCfg, DZ_self, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, reduceIte, one_ne_zero,
      Fin.isValue, Fin.reduceEq] <;> ring

/-! ### The two induction steps -/

variable (C₀ : Cfg)

theorem step_lower (σ : List NN) (q : NN) (L' L : List Ent)
    (hL : ∃ e ∈ L, e.2.1 ≤ 1000) (hL' : ∃ e ∈ L', e.2.1 ≤ 1000)
    (H : ∀ X : Cfg, ((PsiZ L' (ofCfg X) : ℤ) : ℝ) ≤ workFn C₀ σ X)
    (K1 : ∀ e ∈ L', ∀ i : Fin 3, PsiZ L (triUpd e.1 i q) ≤ e.2.1 + DZ (toCfg e.1 i) q) :
    ∀ X : Cfg, ((PsiZ L (ofCfg X) : ℤ) : ℝ) ≤ workFn C₀ (σ ++ [q]) X := by
  intro X
  rw [workFn_snoc (by norm_num) C₀ σ q X]
  apply Finset.le_inf'
  intro Y hY
  obtain ⟨i₀, hi₀⟩ := mem_serving.mp hY
  have hstep : PsiZ L (ofCfg X) ≤ PsiZ L' (ofCfg Y) + MCz (ofCfg Y) (ofCfg X) := by
    have hlip := PsiZ_lip hL (ofCfg Y) (ofCfg X)
    have hle : PsiZ L (ofCfg Y) ≤ PsiZ L' (ofCfg Y) := by
      obtain ⟨e, he, heq⟩ := PsiZ_att hL' (ofCfg Y)
      have hsplit := MCz_split e.1 i₀ Y
      rw [hi₀] at hsplit
      have hA := PsiZ_lip hL (triUpd e.1 i₀ q) (ofCfg Y)
      have hB := K1 e he i₀
      simp only [valAt] at heq
      omega
    omega
  have hcast : ((PsiZ L (ofCfg X) : ℤ) : ℝ)
      ≤ ((PsiZ L' (ofCfg Y) : ℤ) : ℝ) + ((MCz (ofCfg Y) (ofCfg X) : ℤ) : ℝ) := by
    exact_mod_cast hstep
  have hH := H Y
  rw [moveCost_eq Y X]
  linarith

theorem step_upper (σ : List NN) (q : NN) (L' L : List Ent)
    (hL : ∃ e ∈ L, e.2.1 ≤ 1000)
    (H : ∀ X : Cfg, workFn C₀ σ X ≤ ((PsiZ L' (ofCfg X) : ℤ) : ℝ))
    (K2 : ∀ e ∈ L, (e.2.2.1 = q ∨ e.2.2.2.1 = q ∨ e.2.2.2.2 = q) ∧
        PsiZ L' e.2.2 + MCz e.2.2 e.1 ≤ e.2.1) :
    ∀ X : Cfg, workFn C₀ (σ ++ [q]) X ≤ ((PsiZ L (ofCfg X) : ℤ) : ℝ) := by
  intro X
  obtain ⟨e, he, heq⟩ := PsiZ_att hL (ofCfg X)
  obtain ⟨hq, hK⟩ := K2 e he
  have hq' : ∃ i : Fin 3, toCfg e.2.2 i = q := by
    rcases hq with h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  have hA : workFn C₀ (σ ++ [q]) X
      ≤ workFn C₀ σ (toCfg e.2.2) + moveCost (toCfg e.2.2) X :=
    workFn_snoc_le (by norm_num) C₀ σ q X (toCfg e.2.2) hq'
  have hB := H (toCfg e.2.2)
  rw [ofCfg_toCfg] at hB
  have hC : moveCost (toCfg e.2.2) X = ((MCz e.2.2 (ofCfg X) : ℤ) : ℝ) := by
    rw [moveCost_eq, ofCfg_toCfg]
  have hD : PsiZ L' e.2.2 + MCz e.2.2 (ofCfg X) ≤ PsiZ L (ofCfg X) := by
    have := MCz_tri e.2.2 e.1 (ofCfg X)
    simp only [valAt] at heq
    omega
  have hD' : ((PsiZ L' e.2.2 : ℤ) : ℝ) + ((MCz e.2.2 (ofCfg X) : ℤ) : ℝ)
      ≤ ((PsiZ L (ofCfg X) : ℤ) : ℝ) := by exact_mod_cast hD
  rw [hC] at hA
  linarith

/-! ### Unordered work function -/

theorem workFnU_le (σ : List NN) (X : Cfg) (π : Equiv.Perm (Fin 3)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) π

theorem le_workFnU (σ : List NN) (X : Cfg) (b : ℝ)
    (h : ∀ π : Equiv.Perm (Fin 3), b ≤ workFn C₀ σ (X ∘ π)) : b ≤ workFnU C₀ σ X :=
  le_ciInf h

/-- The six permutations of a triple. -/
def permsTri (t : Tri) : List Tri :=
  [(t.1, t.2.1, t.2.2), (t.1, t.2.2, t.2.1), (t.2.1, t.1, t.2.2),
   (t.2.1, t.2.2, t.1), (t.2.2, t.1, t.2.1), (t.2.2, t.2.1, t.1)]

/-- A lower bound for the unordered work function: the minimum over all relabelings. -/
def lowT (L : List Ent) (t : Tri) : ℤ := minList ((permsTri t).map (PsiZ L))

theorem perm_fin3 (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (a, b, c) = ((0 : Fin 3), (1 : Fin 3), (2 : Fin 3)) ∨
    (a, b, c) = ((0 : Fin 3), (2 : Fin 3), (1 : Fin 3)) ∨
    (a, b, c) = ((1 : Fin 3), (0 : Fin 3), (2 : Fin 3)) ∨
    (a, b, c) = ((1 : Fin 3), (2 : Fin 3), (0 : Fin 3)) ∨
    (a, b, c) = ((2 : Fin 3), (0 : Fin 3), (1 : Fin 3)) ∨
    (a, b, c) = ((2 : Fin 3), (1 : Fin 3), (0 : Fin 3)) := by
  revert a b c; decide

theorem lowT_le_perm (L : List Ent) (X : Cfg) (π : Equiv.Perm (Fin 3)) :
    lowT L (ofCfg X) ≤ PsiZ L (ofCfg (X ∘ π)) := by
  have hab : π 0 ≠ π 1 := fun h => by simpa using π.injective h
  have hac : π 0 ≠ π 2 := fun h => by simpa using π.injective h
  have hbc : π 1 ≠ π 2 := fun h => by simpa using π.injective h
  have hmem : ofCfg (X ∘ π) ∈ permsTri (ofCfg X) := by
    have h : ofCfg (X ∘ π) = (X (π 0), X (π 1), X (π 2)) := rfl
    rcases perm_fin3 (π 0) (π 1) (π 2) hab hac hbc with hp|hp|hp|hp|hp|hp <;>
      · rw [h]
        simp only [Prod.mk.injEq] at hp
        obtain ⟨h0, h1, h2⟩ := hp
        rw [h0, h1, h2]
        simp [permsTri, ofCfg]
  exact minList_le (List.mem_map_of_mem hmem)



/-! ## Part 4 : the concrete instance

Initial configuration `C₀ = (p₀,p₄,p₆)`, request sequence `p₅ p₄ p₁ p₂` followed by the
final request `r = p₃`. -/

section Instance

set_option maxRecDepth 40000

/-- The initial configuration `(p₀,p₄,p₆)`. -/
def C0 : Config 3 Pt := ![Pt.p0, Pt.p4, Pt.p6]

/-- The request sequence preceding the final request. -/
def ell : List Pt := [Pt.p5, Pt.p4, Pt.p1, Pt.p2]

/-- The final request. -/
def req : Pt := Pt.p3

/-- The initial configuration, seen inside the antipodal extension. -/
def C0N : Cfg := toCfg (Sum.inl (C0 0), Sum.inl (C0 1), Sum.inl (C0 2))

/-- The request sequence, seen inside the antipodal extension. -/
def sigN : List NN := (ell ++ [req]).map Sum.inl

theorem base_PsiZ (t : Tri) :
    PsiZ L0 t = MCz ((Sum.inl Pt.p0 : NN), (Sum.inl Pt.p4 : NN), (Sum.inl Pt.p6 : NN)) t := by
  have h := MCz_le ((Sum.inl Pt.p0 : NN), (Sum.inl Pt.p4 : NN), (Sum.inl Pt.p6 : NN)) t
  simp only [PsiZ, L0, valAt, List.map_cons, List.map_nil, minList, List.foldr_cons,
    List.foldr_nil]
  omega

theorem base_eq (X : Cfg) : workFn C0N [] X = ((PsiZ L0 (ofCfg X) : ℤ) : ℝ) := by
  rw [workFn_nil, moveCost_eq, base_PsiZ]
  rfl

theorem low0 : ∀ X : Cfg, ((PsiZ L0 (ofCfg X) : ℤ) : ℝ) ≤ workFn C0N [] X :=
  fun X => le_of_eq (base_eq X).symm

theorem upp0 : ∀ X : Cfg, workFn C0N [] X ≤ ((PsiZ L0 (ofCfg X) : ℤ) : ℝ) :=
  fun X => le_of_eq (base_eq X)

theorem low1 : ∀ X : Cfg, ((PsiZ L1 (ofCfg X) : ℤ) : ℝ) ≤ workFn C0N [Sum.inl Pt.p5] X :=
  step_lower C0N [] (Sum.inl Pt.p5) L0 L1 (by decide) (by decide) low0 (by decide)

theorem upp1 : ∀ X : Cfg, workFn C0N [Sum.inl Pt.p5] X ≤ ((PsiZ L1 (ofCfg X) : ℤ) : ℝ) :=
  step_upper C0N [] (Sum.inl Pt.p5) L0 L1 (by decide) upp0 (by decide)

theorem low2 : ∀ X : Cfg,
    ((PsiZ L2 (ofCfg X) : ℤ) : ℝ) ≤ workFn C0N [Sum.inl Pt.p5, Sum.inl Pt.p4] X :=
  step_lower C0N [Sum.inl Pt.p5] (Sum.inl Pt.p4) L1 L2 (by decide) (by decide) low1 (by decide)

theorem upp2 : ∀ X : Cfg,
    workFn C0N [Sum.inl Pt.p5, Sum.inl Pt.p4] X ≤ ((PsiZ L2 (ofCfg X) : ℤ) : ℝ) :=
  step_upper C0N [Sum.inl Pt.p5] (Sum.inl Pt.p4) L1 L2 (by decide) upp1 (by decide)

theorem low3 : ∀ X : Cfg,
    ((PsiZ L3 (ofCfg X) : ℤ) : ℝ) ≤ workFn C0N [Sum.inl Pt.p5, Sum.inl Pt.p4, Sum.inl Pt.p1] X :=
  step_lower C0N [Sum.inl Pt.p5, Sum.inl Pt.p4] (Sum.inl Pt.p1) L2 L3
    (by decide) (by decide) low2 (by decide)

theorem upp3 : ∀ X : Cfg,
    workFn C0N [Sum.inl Pt.p5, Sum.inl Pt.p4, Sum.inl Pt.p1] X ≤ ((PsiZ L3 (ofCfg X) : ℤ) : ℝ) :=
  step_upper C0N [Sum.inl Pt.p5, Sum.inl Pt.p4] (Sum.inl Pt.p1) L2 L3 (by decide) upp2 (by decide)

theorem low4 : ∀ X : Cfg, ((PsiZ L4 (ofCfg X) : ℤ) : ℝ)
    ≤ workFn C0N [Sum.inl Pt.p5, Sum.inl Pt.p4, Sum.inl Pt.p1, Sum.inl Pt.p2] X :=
  step_lower C0N [Sum.inl Pt.p5, Sum.inl Pt.p4, Sum.inl Pt.p1] (Sum.inl Pt.p2) L3 L4
    (by decide) (by decide) low3 (by decide)

theorem upp4 : ∀ X : Cfg,
    workFn C0N [Sum.inl Pt.p5, Sum.inl Pt.p4, Sum.inl Pt.p1, Sum.inl Pt.p2] X
      ≤ ((PsiZ L4 (ofCfg X) : ℤ) : ℝ) :=
  step_upper C0N [Sum.inl Pt.p5, Sum.inl Pt.p4, Sum.inl Pt.p1] (Sum.inl Pt.p2) L3 L4
    (by decide) upp3 (by decide)

/-- The certificate `L5` bounds the work function of the full request sequence from below. -/
theorem low5 : ∀ X : Cfg, ((PsiZ L5 (ofCfg X) : ℤ) : ℝ) ≤ workFn C0N sigN X :=
  step_lower C0N [Sum.inl Pt.p5, Sum.inl Pt.p4, Sum.inl Pt.p1, Sum.inl Pt.p2] (Sum.inl Pt.p3)
    L4 L5 (by decide) (by decide) low4 (by decide)

/-- The certificate `L5` bounds the work function of the full request sequence from above. -/
theorem upp5 : ∀ X : Cfg, workFn C0N sigN X ≤ ((PsiZ L5 (ofCfg X) : ℤ) : ℝ) :=
  step_upper C0N [Sum.inl Pt.p5, Sum.inl Pt.p4, Sum.inl Pt.p1, Sum.inl Pt.p2] (Sum.inl Pt.p3)
    L4 L5 (by decide) upp4 (by decide)

/-- Lower bound for the unordered work function. -/
theorem lowT_le_wU (X : Cfg) : ((lowT L5 (ofCfg X) : ℤ) : ℝ) ≤ workFnU C0N sigN X := by
  apply le_workFnU
  intro pi
  refine le_trans ?_ (low5 (X ∘ pi))
  exact_mod_cast lowT_le_perm L5 X pi

/-- Upper bound for the unordered work function, via any relabeling. -/
theorem wU_le_PsiZ (X : Cfg) (pi : Equiv.Perm (Fin 3)) :
    workFnU C0N sigN X ≤ ((PsiZ L5 (ofCfg (X ∘ pi)) : ℤ) : ℝ) :=
  le_trans (workFnU_le C0N sigN X pi) (upp5 (X ∘ pi))

/-! ### Expanding the anchored potential -/

theorem cfg_inl (x : Fin 3 → Pt) :
    (fun j => Sum.inl (x j) : Cfg) = toCfg (Sum.inl (x 0), Sum.inl (x 1), Sum.inl (x 2)) := by
  funext j; fin_cases j <;> rfl

theorem ckConfig0 (x : Fin 3 → Pt) :
    ckConfigK x 0 = toCfg (Sum.inr (x 0), Sum.inl (x 1), Sum.inl (x 2)) := by
  funext j; fin_cases j <;> rfl

theorem ckConfig1 (x : Fin 3 → Pt) :
    ckConfigK x 1 = toCfg (Sum.inr (x 1), Sum.inr (x 1), Sum.inl (x 2)) := by
  funext j; fin_cases j <;> rfl

theorem ckConfig2 (x : Fin 3 → Pt) :
    ckConfigK x 2 = toCfg (Sum.inr (x 2), Sum.inr (x 2), Sum.inr (x 2)) := by
  funext j; fin_cases j <;> rfl

theorem ckPot_expand (x : Fin 3 → Pt) :
    ckPotAtK 3 Pt 16 hD0 hDle C0 (ell ++ [req]) x
      = workFnU C0N sigN (toCfg (Sum.inl (x 0), Sum.inl (x 1), Sum.inl (x 2)))
        + (workFnU C0N sigN (toCfg (Sum.inr (x 0), Sum.inl (x 1), Sum.inl (x 2)))
          + workFnU C0N sigN (toCfg (Sum.inr (x 1), Sum.inr (x 1), Sum.inl (x 2)))
          + workFnU C0N sigN (toCfg (Sum.inr (x 2), Sum.inr (x 2), Sum.inr (x 2)))) := by
  simp only [ckPotAtK, Fin.sum_univ_three, cfg_inl, ckConfig0, ckConfig1, ckConfig2]
  rfl

/-! ### The two numerical bounds -/

/-- Every anchor tuple whose last coordinate is the request has potential at least `214`. -/
theorem anchored_ge (x : Fin 3 → Pt) (hx : x 2 = Pt.p3) :
    (214 : ℝ) ≤ ckPotAtK 3 Pt 16 hD0 hDle C0 (ell ++ [req]) x := by
  have key : ∀ a b : Pt, (214 : ℤ) ≤
      lowT L5 (Sum.inl a, Sum.inl b, Sum.inl Pt.p3)
      + lowT L5 (Sum.inr a, Sum.inl b, Sum.inl Pt.p3)
      + lowT L5 (Sum.inr b, Sum.inr b, Sum.inl Pt.p3)
      + lowT L5 ((Sum.inr Pt.p3 : NN), (Sum.inr Pt.p3 : NN), (Sum.inr Pt.p3 : NN)) := by decide
  rw [ckPot_expand, hx]
  have h0 := lowT_le_wU (toCfg (Sum.inl (x 0), Sum.inl (x 1), Sum.inl (x 2)))
  have h1 := lowT_le_wU (toCfg (Sum.inr (x 0), Sum.inl (x 1), Sum.inl (x 2)))
  have h2 := lowT_le_wU (toCfg (Sum.inr (x 1), Sum.inr (x 1), Sum.inl (x 2)))
  have h3 := lowT_le_wU (toCfg (Sum.inr (x 2), Sum.inr (x 2), Sum.inr (x 2)))
  rw [ofCfg_toCfg] at h0 h1 h2 h3
  rw [hx] at h0 h1 h2 h3
  have hk := key (x 0) (x 1)
  have hkr : (214 : ℝ) ≤
      ((lowT L5 (Sum.inl (x 0), Sum.inl (x 1), Sum.inl Pt.p3) : ℤ) : ℝ)
      + ((lowT L5 (Sum.inr (x 0), Sum.inl (x 1), Sum.inl Pt.p3) : ℤ) : ℝ)
      + ((lowT L5 (Sum.inr (x 1), Sum.inr (x 1), Sum.inl Pt.p3) : ℤ) : ℝ)
      + ((lowT L5 ((Sum.inr Pt.p3 : NN), (Sum.inr Pt.p3 : NN), (Sum.inr Pt.p3 : NN)) : ℤ) : ℝ) := by
    exact_mod_cast hk
  linarith

/-- The 3-cycle `0 ↦ 2 ↦ 1 ↦ 0` of `Fin 3`. -/
def cyc : Equiv.Perm (Fin 3) := Equiv.swap 1 2 * Equiv.swap 0 1

/-- The transposition of the last two coordinates. -/
def swp : Equiv.Perm (Fin 3) := Equiv.swap 1 2

/-- The anchor tuple `(p₀,p₆,p₁)` has potential at most `212`. -/
theorem upper_212 :
    ckPotAtK 3 Pt 16 hD0 hDle C0 (ell ++ [req]) ![Pt.p0, Pt.p6, Pt.p1] ≤ 212 := by
  have t0 := wU_le_PsiZ (toCfg ((Sum.inl Pt.p0 : NN), (Sum.inl Pt.p6 : NN), (Sum.inl Pt.p1 : NN)))
      swp
  have t1 := wU_le_PsiZ (toCfg ((Sum.inr Pt.p0 : NN), (Sum.inl Pt.p6 : NN), (Sum.inl Pt.p1 : NN)))
      cyc
  have t2 := wU_le_PsiZ (toCfg ((Sum.inr Pt.p6 : NN), (Sum.inr Pt.p6 : NN), (Sum.inl Pt.p1 : NN)))
      cyc
  have t3 := wU_le_PsiZ (toCfg ((Sum.inr Pt.p1 : NN), (Sum.inr Pt.p1 : NN), (Sum.inr Pt.p1 : NN)))
      (Equiv.refl (Fin 3))
  have e0 : PsiZ L5 (ofCfg
      ((toCfg ((Sum.inl Pt.p0 : NN), (Sum.inl Pt.p6 : NN), (Sum.inl Pt.p1 : NN)))
        ∘ swp)) = 29 := by decide
  have e1 : PsiZ L5 (ofCfg
      ((toCfg ((Sum.inr Pt.p0 : NN), (Sum.inl Pt.p6 : NN), (Sum.inl Pt.p1 : NN)))
        ∘ cyc)) = 41 := by decide
  have e2 : PsiZ L5 (ofCfg
      ((toCfg ((Sum.inr Pt.p6 : NN), (Sum.inr Pt.p6 : NN), (Sum.inl Pt.p1 : NN)))
        ∘ cyc)) = 61 := by decide
  have e3 : PsiZ L5 (ofCfg
      ((toCfg ((Sum.inr Pt.p1 : NN), (Sum.inr Pt.p1 : NN), (Sum.inr Pt.p1 : NN)))
        ∘ (Equiv.refl (Fin 3)))) = 81 := by decide
  rw [e0] at t0
  rw [e1] at t1
  rw [e2] at t2
  rw [e3] at t3
  have hv2 : (![Pt.p0, Pt.p6, Pt.p1] : Fin 3 → Pt) 2 = Pt.p1 := rfl
  rw [ckPot_expand, hv2]
  norm_num at t0 t1 t2 t3 ⊢
  linarith

end Instance

end CEK

open KServer CEK in
/-- **The anchor property fails for `k = 3`.** -/
theorem solution : ¬ (∀ (k : ℕ) (hk : 3 ≤ k) (M : Type) [MetricSpace M]
    [Fintype M] (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (l : List M) (r : M),
    ∃ x : Fin k → M, x ⟨k - 1, by omega⟩ = r ∧
      ckPotAtK k M Δ hΔ0 hΔ C₀ (l ++ [r]) x = ckPotK k M Δ hΔ0 hΔ C₀ (l ++ [r])) := by
  intro h
  obtain ⟨x, hx, heq⟩ := h 3 (by norm_num) Pt 16 hD0 hDle C0 ell req
  have hx' : x 2 = Pt.p3 := hx
  have hlow := anchored_ge x hx'
  rw [heq] at hlow
  have hle := ckPotK_le 3 Pt 16 hD0 hDle C0 (ell ++ [req]) ![Pt.p0, Pt.p6, Pt.p1]
  have := upper_212
  linarith
