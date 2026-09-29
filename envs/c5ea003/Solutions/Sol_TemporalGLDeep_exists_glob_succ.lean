-- Prove2me | solution 1 for TemporalGLDeep.exists_glob_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T19:08:03.873713+00:00
-- url     : https://prove2.me/submissions/7e3623b1-d2ca-457c-b006-54978864a3d6

-- Sol generated from Logic/PosetTheory/TemporalGLCompleteness.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalGLCompleteness
import Definitions.Def_Logic_PosetTheory_TemporalGLDeduction
import Definitions.Def_Logic_PosetTheory_TemporalGLFiniteModel
import Definitions.Def_Logic_PosetTheory_TemporalGLSyntax
import Theorems.Thm_TemporalGLDeep_Der_cut
import Theorems.Thm_TemporalGLDeep_Der_glob
import Theorems.Thm_TemporalGLDeep_Der_of_Der_taut
import Theorems.Thm_TemporalGLDeep_exists_world

/-!
# Temporal Gödel–Löb logic: the finite canonical model and completeness

This file closes the last gap in the finite-model conjecture for the calculus TGL.
Rather than building an (infinite) canonical model — which for Gödel–Löb logic is *not*
a legal frame, since converse well-foundedness fails — we build the **finite canonical
model over the subformula closure of a single formula**, using exactly the relations
`filtR` / `filtT` from `TemporalGLFiniteModel.lean`.

Worlds are the consistent "decided subsets" `t ⊆ Cl` of a subformula-closed finite set
`Cl`: the list `gammaList Cl t` asserts every member of `t` and the negation of every
member of `Cl \ t`, and `t` is a world when that list is TGL-consistent.

The two existence lemmas are the mathematical core:

* `exists_box_succ` — if `◻B ∉ t`, there is a world `s` with `filtR Cl t s` and `B ∉ s`.
  Its proof runs the classical **Löb argument**: were the candidate hypothesis list
  inconsistent, boxing it and applying Löb's axiom would force `◻B ∈ t`.
* `exists_glob_succ` — the temporal analogue, whose proof uses `◼`-necessitation, the
  `4` axiom for `◼`, and the interaction axiom `◻A ⟹ ◼◻A`.

Combining these with the truth lemma `can_truth_lemma` yields

* `completeness` — every valid formula is derivable, and
* `finite_model_property` — **the conjecture**: every non-derivable `A` has a
  `TemporalGL.TempFrame` countermodel with at most `2 ^ (2 * subformulaCount A)` worlds.
-/

open TemporalGLDeep

open TemporalGL

/-! ## 1. Subformula-closed sets -/





/-! ## 2. Decided subsets and consistency -/









/-! ## 3. Lists of boxed / temporally boxed members of a world -/



theorem mem_boxList {Cl t : Finset TForm} {x : TForm} (h : x ∈ boxList Cl t) :
    ∃ D, x = ◻D ∧ (◻D) ∈ Cl ∧ (◻D) ∈ t := by
  rw [boxList, List.mem_filter] at h
  obtain ⟨hx, hp⟩ := h
  rw [Finset.mem_toList] at hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  cases x with
  | box D => exact ⟨D, rfl, hx, hp.2⟩
  | atom p => simp [TForm.isBox] at hp
  | bot => simp [TForm.isBox] at hp
  | imp B C => simp [TForm.isBox] at hp
  | glob B => simp [TForm.isBox] at hp

theorem mem_boxList_of {Cl t : Finset TForm} {D : TForm} (h₁ : (◻D) ∈ Cl) (h₂ : (◻D) ∈ t) :
    (◻D) ∈ boxList Cl t := by
  rw [boxList, List.mem_filter]
  exact ⟨Finset.mem_toList.2 h₁, by simp [TForm.isBox, h₂]⟩

theorem mem_globList {Cl t : Finset TForm} {x : TForm} (h : x ∈ globList Cl t) :
    ∃ D, x = ◼D ∧ (◼D) ∈ Cl ∧ (◼D) ∈ t := by
  rw [globList, List.mem_filter] at h
  obtain ⟨hx, hp⟩ := h
  rw [Finset.mem_toList] at hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  cases x with
  | glob D => exact ⟨D, rfl, hx, hp.2⟩
  | atom p => simp [TForm.isGlob] at hp
  | bot => simp [TForm.isGlob] at hp
  | imp B C => simp [TForm.isGlob] at hp
  | box B => simp [TForm.isGlob] at hp

theorem mem_globList_of {Cl t : Finset TForm} {D : TForm} (h₁ : (◼D) ∈ Cl) (h₂ : (◼D) ∈ t) :
    (◼D) ∈ globList Cl t := by
  rw [globList, List.mem_filter]
  exact ⟨Finset.mem_toList.2 h₁, by simp [TForm.isGlob, h₂]⟩

/-! ## 4. The two existence lemmas -/



/-! ## 5. The finite canonical model -/


noncomputable instance (Cl : Finset TForm) : Fintype (CanWorld Cl) := FinsetCoe.fintype _





/-! ## 6. Completeness and the finite model property -/





/-! ## 7. Consequences and non-degeneracy

The results above are only interesting if TGL really is a non-trivial logic in which the
two modalities interact but do not collapse.  This section records that. -/









/-! ## 8. Machine-checked data points for the bound

The bound `2 ^ (2 * subformulaCount A)` is far from tight on concrete formulas; the two
theorems below record explicitly verified minimal countermodels, which are what a
bounded model search would actually return. -/




open TemporalGLDeep in
theorem solution{Cl : Finset TForm} (hCl : Closed Cl) {t : Finset TForm}
    (hcons : Cons Cl t) {B : TForm} (hB : (◼B) ∈ Cl) (hnot : (◼B) ∉ t) :
    ∃ s, s ∈ CanW Cl ∧ filtT Cl t s ∧ B ∉ s := by
  classical
  set G0 : List TForm := globList Cl t with hG0
  set B0 : List TForm := boxList Cl t with hB0
  set D1 : List TForm := G0.map TForm.unglob ++ G0 ++ B0 with hD1
  set D2 : List TForm := D1 ++ [B.neg] with hD2
  have hcons2 : ListCons D2 := by
    intro hbad
    have h1 : Der D1 B := by
      refine Der_of_Der_taut (fun v hall hv => ?_) hbad
      by_contra hnb
      refine hall (fun x hx => ?_)
      rw [hD2] at hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hv x hx
      · have hx' : x = B.neg := by simpa using hx
        subst hx'
        exact hnb
    have h2 : Der (D1.map TForm.glob) (◼B) := Der_glob h1
    have h3 : ∀ x ∈ D1.map TForm.glob, Der (gammaList Cl t) x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      rw [hD1] at hy
      rcases List.mem_append.1 hy with hy | hy
      · rcases List.mem_append.1 hy with hy | hy
        · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
          obtain ⟨E, rfl, hECl, hEt⟩ := mem_globList hz
          exact Der_of_mem (mem_gammaList_pos hECl hEt)
        · obtain ⟨E, rfl, hECl, hEt⟩ := mem_globList hy
          exact Der_mp (Der_of_derivable Derivable.glob4)
            (Der_of_mem (mem_gammaList_pos hECl hEt))
      · obtain ⟨E, rfl, hECl, hEt⟩ := mem_boxList hy
        exact Der_mp (Der_of_derivable Derivable.compatAx)
          (Der_of_mem (mem_gammaList_pos hECl hEt))
    exact hnot (mem_of_Der hcons hB (Der_cut h3 h2))
  obtain ⟨s, hsW, hspos, hsneg⟩ := exists_world Cl D2 hcons2
  have hglobmem : ∀ {E : TForm}, (◼E) ∈ Cl → (◼E) ∈ t → (◼E) ∈ D2 ∧ E ∈ D2 := by
    intro E h1 h2
    constructor
    · rw [hD2]
      exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
        (List.mem_append.2 (Or.inr (mem_globList_of h1 h2))))))
    · rw [hD2]
      exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
        (List.mem_append.2 (Or.inl (List.mem_map.2 ⟨◼E, mem_globList_of h1 h2, rfl⟩))))))
  have hboxmem : ∀ {E : TForm}, (◻E) ∈ Cl → (◻E) ∈ t → (◻E) ∈ D2 := by
    intro E h1 h2
    rw [hD2]
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (mem_boxList_of h1 h2))))
  have hnegmem : B.neg ∈ D2 := by
    rw [hD2]; exact List.mem_append.2 (Or.inr (by simp))
  refine ⟨s, hsW, ⟨?_, ?_⟩, hsneg B hnegmem⟩
  · intro E hECl hEt
    obtain ⟨h1, h2⟩ := hglobmem hECl hEt
    exact ⟨hspos E h2 (hCl.glob hECl), hspos _ h1 hECl⟩
  · intro E hECl hEt
    exact hspos _ (hboxmem hECl hEt) hECl
