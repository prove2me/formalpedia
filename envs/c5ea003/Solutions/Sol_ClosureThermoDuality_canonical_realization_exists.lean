-- Prove2me | solution 1 for ClosureThermoDuality.canonical_realization_exists
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T01:32:46.709681+00:00
-- url     : https://prove2.me/submissions/5f3d07cf-f5c5-40d2-a720-522f2d1a2898

import Mathlib
import Definitions.Def_Bridges_HilbertSpace_ClosureThermodynamicComputationDuality

open ClosureThermoDuality Finset in
theorem solution {n : ℕ} (D : DissipData n) (hn : 0 < D.numProfs) :
    ∃ (T : ThermoComp (Fin D.numProfs) n),
      T.Separated ∧ Nonempty (T.Realizes D) := by
  -- closed sets form the chain `{j : j ≤ k}`, one per data index `k`
  let c : Finset (Fin D.numProfs) → Finset (Fin D.numProfs) :=
    fun A => univ.filter (fun j => j.val ≤ A.sup Fin.val)
  have hsub : ∀ A, A ⊆ c A := fun A a ha => by
    simp only [c, mem_filter, mem_univ, true_and]
    exact Finset.le_sup (f := Fin.val) ha
  have hsup : ∀ A, (c A).sup Fin.val = A.sup Fin.val := fun A => by
    apply le_antisymm
    · exact Finset.sup_le fun j hj => by simpa [c] using hj
    · exact Finset.sup_mono (hsub A)
  have hidem : ∀ A, c (c A) = c A := fun A => by
    change univ.filter (fun j : Fin D.numProfs => j.val ≤ (c A).sup Fin.val) = c A
    rw [hsup]
  have hlt : ∀ A : Finset (Fin D.numProfs), A.sup Fin.val < D.numProfs := fun A =>
    (Finset.sup_lt_iff (by simpa using hn)).2 fun b _ => b.isLt
  let idx : Finset (Fin D.numProfs) → Fin D.numProfs := fun A => ⟨A.sup Fin.val, hlt A⟩
  let T : ThermoComp (Fin D.numProfs) n :=
    { cl := c
      extensive := hsub
      mono := fun {A B} h => by
        intro j hj
        simp only [c, mem_filter, mem_univ, true_and] at hj ⊢
        exact hj.trans (Finset.sup_mono h)
      idem := hidem
      energy := fun _ => 0
      energy_mono := fun _ => le_rfl
      dissip := fun i A => D.prof (idx A) i }
  refine ⟨T, ?_, ⟨{ map := fun p => idx p.val, map_surj := ?_, map_compat := ?_ }⟩⟩
  · intro A B hA hB hp
    have hA' : c A = A := hA
    have hB' : c B = B := hB
    have hpr : D.prof (idx (c A)) = D.prof (idx (c B)) := funext fun i => congrFun hp i
    have hs : A.sup Fin.val = B.sup Fin.val := by
      have h := congrArg Fin.val (D.prof_inj hpr)
      simpa [idx, hsup] using h
    rw [← hA', ← hB']
    change univ.filter (fun j : Fin D.numProfs => j.val ≤ A.sup Fin.val)
      = univ.filter (fun j : Fin D.numProfs => j.val ≤ B.sup Fin.val)
    rw [hs]
  · intro k
    refine ⟨⟨c {k}, hidem {k}⟩, ?_⟩
    apply Fin.ext
    change (c {k}).sup Fin.val = k.val
    rw [hsup, Finset.sup_singleton]
  · intro p
    have hp : c p.1 = p.1 := p.2
    funext i
    change D.prof (idx (c p.1)) i = D.prof (idx p.1) i
    rw [hp]
