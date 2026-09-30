-- Prove2me | solution 1 for lean_workbook_plus_10787
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:04:41.987217+00:00
-- url     : https://prove2.me/submissions/0623148a-8dec-40e5-bfbf-d7622d0e8236

import Mathlib

namespace InvolutionEvenOddDecomposition

universe u
variable {α : Type u}

noncomputable def evenPart (s : α → α) (g : α → ℝ) (x : α) : ℝ := (g x + g (s x)) / 2

noncomputable def oddPart (s : α → α) (g : α → ℝ) (x : α) : ℝ := (g x - g (s x)) / 2

def Equations (s : α → α) (g h k : α → ℝ) : Prop :=
  ∀ x, g x = h x + k x ∧ g (s x) = h x - k x

def IsDecomposition (s : α → α) (g : α → ℝ) (p : (α → ℝ) × (α → ℝ)) : Prop :=
  ∀ x, g x = p.1 x + p.2 x ∧ p.1 (s x) = p.1 x ∧ p.2 (s x) = -p.2 x

theorem parts_equations (s : α → α) (g : α → ℝ) :
    Equations s g (evenPart s g) (oddPart s g) := by
  intro x
  dsimp [evenPart, oddPart]
  constructor <;> ring

theorem equations_iff (s : α → α) (g h k : α → ℝ) :
    Equations s g h k ↔ h = evenPart s g ∧ k = oddPart s g := by
  constructor
  · intro he
    constructor
    · funext x
      have hx := he x
      dsimp [evenPart]
      linarith [hx.1, hx.2]
    · funext x
      have hx := he x
      dsimp [oddPart]
      linarith [hx.1, hx.2]
  · rintro ⟨rfl, rfl⟩
    exact parts_equations s g

theorem parts_symmetries (s : α → α) (hs : Function.Involutive s) (g : α → ℝ)
    (x : α) : evenPart s g (s x) = evenPart s g x ∧
      oddPart s g (s x) = -oddPart s g x := by
  simp only [evenPart, oddPart, hs x]
  constructor <;> ring

theorem decomposition_iff (s : α → α) (hs : Function.Involutive s)
    (g : α → ℝ) (p : (α → ℝ) × (α → ℝ)) :
    IsDecomposition s g p ↔ p.1 = evenPart s g ∧ p.2 = oddPart s g := by
  constructor
  · intro hp
    apply (equations_iff s g p.1 p.2).mp
    intro x
    refine ⟨(hp x).1, ?_⟩
    have hg := (hp (s x)).1
    rw [(hp x).2.1, (hp x).2.2] at hg
    simpa only [sub_eq_add_neg] using hg
  · rintro ⟨hh, hk⟩ x
    rw [hh, hk]
    exact ⟨(parts_equations s g x).1, parts_symmetries s hs g x⟩

theorem unique_decomposition (s : α → α) (hs : Function.Involutive s) (g : α → ℝ) :
    ∃! p : (α → ℝ) × (α → ℝ), IsDecomposition s g p := by
  refine ⟨(evenPart s g, oddPart s g), ?_, ?_⟩
  · exact (decomposition_iff s hs g _).mpr ⟨rfl, rfl⟩
  · intro p hp
    obtain ⟨hh, hk⟩ := (decomposition_iff s hs g p).mp hp
    exact Prod.ext hh hk

theorem odd_at_fixed_point (s : α → α) (g : α → ℝ) (x : α) (hx : s x = x) :
    oddPart s g x = 0 := by
  simp only [oddPart, hx, sub_self, zero_div]

theorem projection_identities (s : α → α) (hs : Function.Involutive s) (g : α → ℝ) :
    evenPart s (evenPart s g) = evenPart s g ∧
      oddPart s (oddPart s g) = oddPart s g ∧
      evenPart s (oddPart s g) = (fun _ => 0) ∧
      oddPart s (evenPart s g) = (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    funext x
    simp only [evenPart, oddPart, hs x]
    ring

end InvolutionEvenOddDecomposition

theorem solution (g h k : ℝ → ℝ) :
    (∀ x, g x = h x + k x ∧ g (-x) = h x - k x) ↔
      ∀ x, h x = (g x + g (-x)) / 2 ∧ k x = (g x - g (-x)) / 2 := by
  constructor
  · intro he
    obtain ⟨hh, hk⟩ :=
      (InvolutionEvenOddDecomposition.equations_iff (fun x : ℝ => -x) g h k).mp he
    intro x
    exact ⟨congrFun hh x, congrFun hk x⟩
  · intro he
    apply (InvolutionEvenOddDecomposition.equations_iff (fun x : ℝ => -x) g h k).mpr
    exact ⟨funext (fun x => (he x).1), funext (fun x => (he x).2)⟩

#print axioms InvolutionEvenOddDecomposition.parts_equations
#print axioms InvolutionEvenOddDecomposition.equations_iff
#print axioms InvolutionEvenOddDecomposition.parts_symmetries
#print axioms InvolutionEvenOddDecomposition.decomposition_iff
#print axioms InvolutionEvenOddDecomposition.unique_decomposition
#print axioms InvolutionEvenOddDecomposition.odd_at_fixed_point
#print axioms InvolutionEvenOddDecomposition.projection_identities
#print axioms solution
