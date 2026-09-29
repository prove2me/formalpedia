-- Prove2me | solution 1 for FreeMonoidShuffle.count_shuf_eq_count_unsh
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T02:11:07.032361+00:00
-- url     : https://prove2.me/submissions/78411762-5021-4336-976c-4cca88f4135a

-- Thm stub generated from Novelty/FreeMonoidUnshuffle.lean
import Mathlib
import Definitions.Def_Novelty_FreeMonoidShuffle
import Definitions.Def_Novelty_FreeMonoidUnshuffle
/-
# The unshuffle coproduct and shuffle/unshuffle duality

Continuation of `Novelty.FreeMonoidShuffle`.  We introduce the *unshuffle* coproduct

`Δ_⧢ (w) = Σ_{w = u ⧢ v} u ⊗ v`

defined by the recursion `Δ_⧢(a·w) = (a ⊗ 1 + 1 ⊗ a) · Δ_⧢(w)` (the unique
concatenation-algebra morphism making every letter primitive), and prove:

* `count_shuf_eq_count_unsh` : **duality** — the multiplicity of `w` in the shuffle
  `u ⧢ v` equals the multiplicity of `(u,v)` in the unshuffle of `w`.  This is the
  statement that the shuffle product and the unshuffle coproduct are transposes of one
  another for the canonical pairing on words.
* `unsh_append` : the unshuffle coproduct is multiplicative for concatenation
  (the bialgebra axiom for `(K⟨X⟩, concatenation, Δ_⧢)`).
* `unsh_coassoc` : the unshuffle coproduct is coassociative.
* `unsh_card`, `unsh_length_mem` : grading data.
-/

open FreeMonoidShuffle

variable {X : Type*}

/-! ## The unshuffle coproduct -/






/-! ## Counting lemmas -/

variable [DecidableEq X]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace FMS

theorem shuf_nil_left (v : List X) : shuf ([] : List X) v = {v} := by
  rw [shuf]

theorem shuf_nil_right (u : List X) : shuf u ([] : List X) = {u} := by
  cases u with
  | nil => rw [shuf]
  | cons a u =>
    rw [shuf]
    simp

theorem shuf_cons (a : X) (u : List X) (b : X) (v : List X) :
    shuf (a :: u) (b :: v)
      = ((shuf u (b :: v)).map (a :: ·)) + ((shuf (a :: u) v).map (b :: ·)) := by
  rw [shuf]

theorem unsh_nil : unsh ([] : List X) = {([], [])} := rfl

theorem unsh_cons (a : X) (w : List X) :
    unsh (a :: w)
      = ((unsh w).map (fun p => (a :: p.1, p.2))) + ((unsh w).map (fun p => (p.1, a :: p.2))) :=
  rfl

theorem length_of_mem_shuf (u : List X) :
    ∀ (v z : List X), z ∈ shuf u v → z.length = u.length + v.length := by
  induction u with
  | nil =>
    intro v z hz
    rw [shuf_nil_left, Multiset.mem_singleton] at hz
    subst hz; simp
  | cons a u ihu =>
    intro v
    induction v with
    | nil =>
      intro z hz
      rw [shuf_nil_right, Multiset.mem_singleton] at hz
      subst hz; simp
    | cons b v ihv =>
      intro z hz
      rw [shuf_cons] at hz
      rcases Multiset.mem_add.1 hz with h | h
      · obtain ⟨z', hz', rfl⟩ := Multiset.mem_map.1 h
        have hl := ihu (b :: v) z' hz'
        simp only [List.length_cons] at hl ⊢
        omega
      · obtain ⟨z', hz', rfl⟩ := Multiset.mem_map.1 h
        have hl := ihv z' hz'
        simp only [List.length_cons] at hl ⊢
        omega

theorem count_map_consL [DecidableEq X] (c : X) (s : Multiset (List X × List X)) (u v : List X) :
    Multiset.count (c :: u, v) (s.map (fun p => (c :: p.1, p.2))) = Multiset.count (u, v) s := by
  have hinj : Function.Injective (fun p : List X × List X => (c :: p.1, p.2)) := by
    rintro ⟨x1, x2⟩ ⟨y1, y2⟩ hxy; simpa using hxy
  exact Multiset.count_map_eq_count' _ _ hinj (u, v)

theorem count_map_consR [DecidableEq X] (c : X) (s : Multiset (List X × List X)) (u v : List X) :
    Multiset.count (u, c :: v) (s.map (fun p => (p.1, c :: p.2))) = Multiset.count (u, v) s := by
  have hinj : Function.Injective (fun p : List X × List X => (p.1, c :: p.2)) := by
    rintro ⟨x1, x2⟩ ⟨y1, y2⟩ hxy; simpa using hxy
  exact Multiset.count_map_eq_count' _ _ hinj (u, v)

theorem count_map_consL_zero [DecidableEq X] (c : X) (s : Multiset (List X × List X)) (u v : List X)
    (h : u.head? ≠ some c) :
    Multiset.count (u, v) (s.map (fun p => (c :: p.1, p.2))) = 0 := by
  rw [Multiset.count_eq_zero]
  intro hm
  obtain ⟨p, -, hp⟩ := Multiset.mem_map.1 hm
  have hfst : c :: p.1 = u := by simpa using congrArg Prod.fst hp
  exact h (by rw [← hfst]; rfl)

theorem count_map_consR_zero [DecidableEq X] (c : X) (s : Multiset (List X × List X)) (u v : List X)
    (h : v.head? ≠ some c) :
    Multiset.count (u, v) (s.map (fun p => (p.1, c :: p.2))) = 0 := by
  rw [Multiset.count_eq_zero]
  intro hm
  obtain ⟨p, -, hp⟩ := Multiset.mem_map.1 hm
  have hsnd : c :: p.2 = v := by simpa using congrArg Prod.snd hp
  exact h (by rw [← hsnd]; rfl)

theorem count_map_consList [DecidableEq X] (a : X) (s : Multiset (List X)) (z : List X) :
    Multiset.count (a :: z) (s.map (a :: ·)) = Multiset.count z s := by
  have hinj : Function.Injective (fun z : List X => a :: z) := by
    intro x y hxy; simpa using hxy
  exact Multiset.count_map_eq_count' _ _ hinj z

theorem count_map_consList_zero [DecidableEq X] (a : X) (s : Multiset (List X)) (z : List X)
    (h : z.head? ≠ some a) : Multiset.count z (s.map (a :: ·)) = 0 := by
  rw [Multiset.count_eq_zero]
  intro hm
  obtain ⟨y, -, hy⟩ := Multiset.mem_map.1 hm
  exact h (by rw [← hy]; rfl)

theorem count_shuf_eq_count_unsh [DecidableEq X] (w : List X) :
    ∀ u v : List X, Multiset.count w (shuf u v) = Multiset.count (u, v) (unsh w) := by
  induction w with
  | nil =>
    intro u v
    rw [unsh_nil]
    by_cases h : u = [] ∧ v = []
    · obtain ⟨rfl, rfl⟩ := h
      rw [shuf_nil_left]
      simp
    · have hne : ((u, v) : List X × List X) ≠ ([], []) := by
        intro hc
        exact h ⟨by simpa using congrArg Prod.fst hc, by simpa using congrArg Prod.snd hc⟩
      rw [Multiset.count_singleton, if_neg hne, Multiset.count_eq_zero]
      intro hm
      have hl := length_of_mem_shuf u v [] hm
      simp only [List.length_nil] at hl
      exact h ⟨List.length_eq_zero_iff.1 (by omega), List.length_eq_zero_iff.1 (by omega)⟩
  | cons c w ih =>
    intro u v
    rw [unsh_cons, Multiset.count_add]
    match u, v with
    | [], [] =>
      rw [shuf_nil_left, count_map_consL_zero c _ _ _ (by simp),
        count_map_consR_zero c _ _ _ (by simp), Multiset.count_singleton, if_neg (by simp)]
    | [], b :: v =>
      rw [shuf_nil_left, count_map_consL_zero c _ _ _ (by simp), zero_add]
      by_cases hbc : b = c
      · rw [hbc, count_map_consR, ← ih [] v, shuf_nil_left,
          Multiset.count_singleton, Multiset.count_singleton]
        simp
      · rw [count_map_consR_zero c _ _ _ (by simpa using hbc), Multiset.count_singleton, if_neg]
        intro hc2
        simp only [List.cons.injEq] at hc2
        exact hbc hc2.1.symm
    | a :: u, [] =>
      rw [shuf_nil_right, count_map_consR_zero c _ _ _ (by simp), add_zero]
      by_cases hac : a = c
      · rw [hac, count_map_consL, ← ih u [], shuf_nil_right,
          Multiset.count_singleton, Multiset.count_singleton]
        simp
      · rw [count_map_consL_zero c _ _ _ (by simpa using hac), Multiset.count_singleton, if_neg]
        intro hc2
        simp only [List.cons.injEq] at hc2
        exact hac hc2.1.symm
    | a :: u, b :: v =>
      rw [shuf_cons, Multiset.count_add]
      by_cases hac : a = c
      · rw [hac, count_map_consList, count_map_consL, ih u (b :: v)]
        by_cases hbc : b = c
        · rw [hbc, count_map_consList, count_map_consR, ih (c :: u) v]
        · rw [count_map_consList_zero b _ _ (by simpa using fun hh => hbc hh.symm),
            count_map_consR_zero c _ _ _ (by simpa using hbc)]
      · rw [count_map_consList_zero a _ _ (by simpa using fun hh => hac hh.symm),
          count_map_consL_zero c _ _ _ (by simpa using hac), zero_add, zero_add]
        by_cases hbc : b = c
        · rw [hbc, count_map_consList, count_map_consR, ih (a :: u) v]
        · rw [count_map_consList_zero b _ _ (by simpa using fun hh => hbc hh.symm),
            count_map_consR_zero c _ _ _ (by simpa using hbc)]


/-! ### Coassociativity -/

end FMS

theorem solution (u v w : List X) :
    Multiset.count w (shuf u v) = Multiset.count (u, v) (unsh w) :=
  FMS.count_shuf_eq_count_unsh w u v
