-- Prove2me | solution 1 for Geometry.KernelPatterns.card_fibre_ordPatterns
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:06:15.843218+00:00
-- url     : https://prove2.me/submissions/baa314ff-5712-410f-aa7d-ce6be1c7f598

-- Sol generated from Geometry/KernelPatterns/Fubini.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Core
import Definitions.Def_Geometry_KernelPatterns_Faces
import Definitions.Def_Geometry_KernelPatterns_Fubini
import Definitions.Def_Geometry_KernelPatterns_Stirling
import Theorems.Thm_Geometry_KernelPatterns_mem_ordPatterns
import Theorems.Thm_Geometry_KernelPatterns_pat_rank
import Theorems.Thm_Geometry_KernelPatterns_rank_congr
import Theorems.Thm_Geometry_KernelPatterns_rank_idem
import Theorems.Thm_Geometry_KernelPatterns_rank_val
import Theorems.Thm_Geometry_KernelPatterns_rank_val_eq_of_surjective

/-!
# The Fubini (ordered Bell) formula for faces of the braid arrangement

`Faces.lean` introduced the *ordered pattern* `rank v` of a tuple and showed it
is a complete invariant of the face of the braid arrangement spanned by `v`.
This file counts the ordered patterns exactly:

`#(ordPatterns n) = ∑_{k ≤ n} S(n, k) · k!`,

the ordered Bell (Fubini) numbers `1, 1, 3, 13, 75, 541` (OEIS A000670), where
`S(n, k) = Nat.stirlingSecond n k` counts the kernel patterns with `k` blocks
(`Stirling.lean`).  Geometrically: every face of the braid arrangement is
obtained from a flat (a kernel pattern, i.e. a set partition into `k` blocks) by
choosing one of the `k!` linear orders of its blocks.

The proof fibres `ordPatterns n` first over the number of blocks and then over
the underlying kernel pattern, and identifies each fibre with `Equiv.Perm (Fin k)`
by transporting along the order isomorphism `Fin k ≃o` (block representatives).

Main results:
* `card_reps` — the block representatives biject with the distinct values.
* `rank_val_eq_of_surjective` — for a *surjective* `v : Fin n → Fin k` the rank
  function is the tuple itself; this is the rigidity statement that makes the
  fibres rigid.
* `card_fibre_ordPatterns` — the ordered patterns refining a fixed kernel
  pattern with `k` blocks number exactly `k!`.
* `card_ordPatternsWith` — `#{faces with k blocks} = S(n,k) · k!`.
* `card_ordPatterns_eq_sum_stirlingSecond` — the Fubini formula.
-/

open Geometry.KernelPatterns

open Finset

variable {n k : ℕ} {X : Type*} [LinearOrder X]

/-! ### Block representatives -/


@[simp] lemma mem_reps {v : Fin n → X} {j : Fin n} : j ∈ reps v ↔ pat v j = j := by
  simp [reps]

/-- The representatives biject with the distinct values. -/
theorem card_reps (v : Fin n → X) : (reps v).card = (univ.image v).card := by
  refine Finset.card_bij (fun j _ => v j) (fun a _ => Finset.mem_image_of_mem _ (mem_univ a))
    ?_ ?_
  · intro a ha b hb hab
    rw [mem_reps] at ha hb
    rw [← ha, ← hb]
    exact pat_eq_iff.2 hab
  · intro b hb
    simp only [Finset.mem_image, mem_univ, true_and] at hb
    obtain ⟨i, rfl⟩ := hb
    exact ⟨pat v i, by rw [mem_reps]; exact pat_apply_pat v i, apply_pat v i⟩



/-! ### Rank versus the number of blocks -/

theorem rank_val_lt_card_reps (v : Fin n → X) (i : Fin n) :
    (rank v i : ℕ) < (reps v).card := by
  have hsub : (univ.filter fun j => pat v j = j ∧ v j < v i) ⊂ reps v := by
    refine ⟨fun j hj => ?_, fun hcon => ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at hj
      rw [mem_reps]; exact hj.1
    · have hmem : pat v i ∈ reps v := by rw [mem_reps]; exact pat_apply_pat v i
      have hcon' := hcon hmem
      simp at hcon'
  rw [rank_val]
  exact Finset.card_lt_card hsub

/-- An ordered pattern takes values below its number of blocks. -/
theorem val_lt_card_image_of_rank_eq {r : Fin n → Fin n} (hr : rank r = r) (i : Fin n) :
    (r i : ℕ) < (univ.image r).card := by
  have h := rank_val_lt_card_reps r i
  rw [hr] at h
  rwa [card_reps] at h


/-! ### The fibres of `pat` on ordered patterns -/


/-! ### The Fubini formula -/






/-! ### Faces versus chambers and flats -/




open Geometry.KernelPatterns in
theorem solution{p : Fin n → Fin n} (hp : pat p = p)
    (hk : (univ.image p).card = k) :
    ((ordPatterns n).filter fun r => pat r = p).card = k.factorial := by
  classical
  have hcard : (reps p).card = k := by rw [card_reps, hk]
  set e := (reps p).orderIsoOfFin hcard with he
  have hmem : ∀ i, p i ∈ reps p := fun i => by
    rw [mem_reps, hp]
    have h := pat_apply_pat p i
    rwa [hp] at h
  have hfix : ∀ x : Fin k, p ((e x : Fin n)) = (e x : Fin n) := by
    intro x
    have h2 := (e x).2
    rw [mem_reps, hp] at h2
    exact h2
  have hkey : ∀ x : Fin k, e.symm ⟨p ((e x : Fin n)), hmem _⟩ = x := by
    intro x
    have hsub : (⟨p ((e x : Fin n)), hmem _⟩ : ↥(reps p)) = e x := Subtype.ext (hfix x)
    rw [hsub]
    exact e.symm_apply_apply x
  -- the tuple attached to a permutation of the blocks
  set v : Equiv.Perm (Fin k) → Fin n → Fin k :=
    fun σ i => σ (e.symm ⟨p i, hmem i⟩) with hv
  have hvsurj : ∀ σ, Function.Surjective (v σ) := by
    intro σ x
    refine ⟨(e (σ.symm x) : Fin n), ?_⟩
    simp only [hv, hkey (σ.symm x)]
    exact σ.apply_symm_apply x
  have hvpat : ∀ σ, pat (v σ) = p := by
    intro σ
    have hcg : pat (v σ) = pat p := by
      refine pat_congr fun a b => ?_
      simp [hv, Subtype.ext_iff]
    rw [hcg, hp]
  have hbij : (univ : Finset (Equiv.Perm (Fin k))).card
      = ((ordPatterns n).filter fun r => pat r = p).card := by
    refine Finset.card_bij (fun σ _ => rank (v σ)) ?_ ?_ ?_
    · intro σ _
      simp only [mem_filter]
      exact ⟨(mem_ordPatterns _).2 (rank_idem _), by rw [pat_rank]; exact hvpat σ⟩
    · intro σ _ τ _ hst
      have hst' : rank (v σ) = rank (v τ) := hst
      have hval : ∀ i, v σ i = v τ i := by
        intro i
        apply Fin.ext
        rw [← rank_val_eq_of_surjective (hvsurj σ) i, ← rank_val_eq_of_surjective (hvsurj τ) i,
          hst']
      apply Equiv.ext
      intro x
      have := hval ((e x : Fin n))
      simpa only [hv, hkey x] using this
    · intro r hr
      simp only [mem_filter] at hr
      obtain ⟨hr1, hr2⟩ := hr
      have hrr : rank r = r := (mem_ordPatterns r).1 hr1
      have hrepsr : reps r = reps p := by
        ext j
        simp [hr2, hp]
      have hkr : (univ.image r).card = k := by
        rw [← card_reps, hrepsr, hcard]
      have hlt : ∀ x : Fin k, (r ((e x : Fin n)) : ℕ) < k := by
        intro x
        have := val_lt_card_image_of_rank_eq hrr ((e x : Fin n))
        rwa [hkr] at this
      set f : Fin k → Fin k := fun x => ⟨(r ((e x : Fin n)) : ℕ), hlt x⟩ with hf
      have hfinj : Function.Injective f := by
        intro x y hxy
        have h1 : r ((e x : Fin n)) = r ((e y : Fin n)) := by
          apply Fin.ext
          simpa [hf] using congrArg Fin.val hxy
        have h2 : pat r ((e x : Fin n)) = pat r ((e y : Fin n)) := pat_eq_iff.2 h1
        rw [hr2] at h2
        rw [hfix x, hfix y] at h2
        exact e.injective (Subtype.ext h2)
      set σ : Equiv.Perm (Fin k) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfinj)
        with hsig
      refine ⟨σ, Finset.mem_univ _, ?_⟩
      have hvv : ∀ i, (v σ i : ℕ) = (r i : ℕ) := by
        intro i
        have hpi : (⟨p i, hmem i⟩ : ↥(reps p)) = e (e.symm ⟨p i, hmem i⟩) :=
          (e.apply_symm_apply _).symm
        have hei : ((e (e.symm ⟨p i, hmem i⟩) : Fin n)) = p i := by
          rw [← hpi]
        have hrp : r (p i) = r i := by
          have := apply_pat r i
          rwa [hr2] at this
        simp only [hv, hsig, Equiv.ofBijective_apply, hf, hei, hrp]
      have hrk : rank (v σ) = rank r := by
        refine rank_congr fun a b => ?_
        rw [Fin.lt_def, Fin.lt_def, hvv a, hvv b]
      show rank (v σ) = r
      rw [hrk, hrr]
  rw [← hbij, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
