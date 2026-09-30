-- Prove2me | solution 1 for triangle_free_chromatic_number
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:32:48.608941+00:00
-- url     : https://prove2.me/submissions/01a217a8-fede-4707-a4ea-62262cc1a64b

import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace ShiftGraphConstruction

private abbrev Vertex (N : ℕ) := {p : Fin N × Fin N // p.1 < p.2}

private def graph (N : ℕ) : SimpleGraph (Vertex N) where
  Adj v w := v.val.2 = w.val.1 ∨ w.val.2 = v.val.1
  symm := by intro v w h; exact h.symm
  loopless := ⟨by
    intro v h
    have hv := v.property
    rcases h with h | h <;> exact (ne_of_lt hv) h.symm⟩

private instance (N : ℕ) : DecidableRel (graph N).Adj := fun v w =>
  inferInstanceAs (Decidable (v.val.2 = w.val.1 ∨ w.val.2 = v.val.1))

private theorem color_bound (N k : ℕ) (c : Vertex N → Fin k)
    (hc : ∀ v w, (graph N).Adj v w → c v ≠ c w) : N ≤ 2 ^ k := by
  classical
  let colors : Fin N → Set (Fin k) := fun i =>
    {a | ∃ j : Fin N, ∃ h : i < j, c ⟨(i, j), h⟩ = a}
  have hsep {i j : Fin N} (hij : i < j) : colors i ≠ colors j := by
    intro heq
    let v : Vertex N := ⟨(i, j), hij⟩
    have hmem : c v ∈ colors i := ⟨j, hij, rfl⟩
    rw [heq] at hmem
    obtain ⟨l, hjl, hcol⟩ := hmem
    exact hc v ⟨(j, l), hjl⟩ (Or.inl rfl) hcol.symm
  have hinj : Function.Injective colors := by
    intro i j h
    rcases lt_trichotomy i j with hij | heq | hji
    · exact False.elim (hsep hij h)
    · exact heq
    · exact False.elim (hsep hji h.symm)
  simpa using Fintype.card_le_of_injective colors hinj

private theorem triangle_free (N : ℕ) :
    ¬ ∃ a b c : Vertex N, (graph N).Adj a b ∧
      (graph N).Adj b c ∧ (graph N).Adj a c := by
  rintro ⟨a, b, c, hab, hbc, hac⟩
  have ha := a.property
  have hb := b.property
  have hc := c.property
  change (a.val.2 = b.val.1 ∨ b.val.2 = a.val.1) at hab
  change (b.val.2 = c.val.1 ∨ c.val.2 = b.val.1) at hbc
  change (a.val.2 = c.val.1 ∨ c.val.2 = a.val.1) at hac
  simp only [Fin.ext_iff] at hab hbc hac
  omega

end ShiftGraphConstruction

theorem solution : ∀ k : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n))
    (hD : DecidableRel G.Adj), G.chromaticNumber ≥ k ∧
      ¬ ∃ a b c : Fin n, G.Adj a b ∧ G.Adj b c ∧ G.Adj a c := by
  classical
  intro k
  let N := 2 ^ k + 1
  let V := ShiftGraphConstruction.Vertex N
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let G : SimpleGraph (Fin (Fintype.card V)) :=
    (ShiftGraphConstruction.graph N).comap e.symm
  refine ⟨Fintype.card V, G, inferInstance, ?_, ?_⟩
  · by_contra! h
    obtain ⟨c⟩ := SimpleGraph.chromaticNumber_le_iff_colorable.mp (le_of_lt h)
    have hc : ∀ v w : V, (ShiftGraphConstruction.graph N).Adj v w →
        c (e v) ≠ c (e w) := by
      intro v w hvw
      apply c.valid
      simpa [G] using hvw
    have hb := ShiftGraphConstruction.color_bound N k (fun v => c (e v)) hc
    dsimp [N] at hb
    omega
  · rintro ⟨a, b, c, hab, hbc, hac⟩
    exact ShiftGraphConstruction.triangle_free N
      ⟨e.symm a, e.symm b, e.symm c, hab, hbc, hac⟩
