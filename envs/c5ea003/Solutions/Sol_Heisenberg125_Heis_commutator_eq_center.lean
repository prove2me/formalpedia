-- Prove2me | solution 1 for Heisenberg125.Heis.commutator_eq_center
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T22:52:20.661875+00:00
-- url     : https://prove2.me/submissions/e07c85b2-cc0b-4ec9-aedd-1efdcf9e311e

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_Structure
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} : commutator (Heis p) = Subgroup.center (Heis p) := by
  -- `[g, h] = (0, 0, g.a h.b - h.a g.b)`
  have hcomm : ∀ g h : Heis p, g * h * g⁻¹ * h⁻¹ = ⟨0, 0, g.a * h.b - h.a * g.b⟩ := by
    intro g h
    ext <;> simp <;> ring
  -- the centre is `{(0, 0, c)}`
  have hcenter : ∀ g : Heis p, g ∈ Subgroup.center (Heis p) ↔ g.a = 0 ∧ g.b = 0 := by
    intro g
    rw [Subgroup.mem_center_iff]
    constructor
    · intro hg
      have h1 := congrArg Heis.c (hg (y p))
      have h2 := congrArg Heis.c (hg (x p))
      simp only [mul_c, y, x] at h1 h2
      exact ⟨by linear_combination -h1, by linear_combination h2⟩
    · rintro ⟨ha, hb⟩ h
      ext <;> simp [ha, hb] <;> ring
  apply le_antisymm
  · -- every commutator is central
    rw [commutator, Subgroup.commutator_le]
    intro g _ h _
    rw [commutatorElement_def, hcenter, hcomm]
    exact ⟨rfl, rfl⟩
  · -- every central element `(0, 0, c)` is the commutator `[x, (0, c, 0)]`
    intro g hg
    obtain ⟨ha, hb⟩ := (hcenter g).mp hg
    have hg' : g = x p * (⟨0, g.c, 0⟩ : Heis p) * (x p)⁻¹ * (⟨0, g.c, 0⟩ : Heis p)⁻¹ := by
      rw [hcomm]
      ext <;> simp [x, ha, hb]
    rw [hg', ← commutatorElement_def, commutator]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
