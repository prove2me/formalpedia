-- Prove2me | solution 1 for mme_complete_split_exact_type_uniform_chunk_shuffle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T04:35:44.702341+00:00
-- url     : https://prove2.me/submissions/cea63bea-9d9f-412d-afaf-1de41071008f

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_dwz_hole_cover_data
import Theorems.Thm_mme_dwz_available_block_shuffle_of_pretransitive_action
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Perm

open MME MME.CompleteSplit MME.DWZComponentRestriction MME.DWZSquare
open scoped Classical NNReal

set_option autoImplicit false
set_option warningAsError true

private theorem count_reindex {ell N : ℕ}
    (w : PowIndex (CompleteWord ell) N) (e : Equiv.Perm (Fin N))
    (sigma : CompleteWord ell) :
    wordCount id (PowIndex.reindex e w) sigma = wordCount id w sigma := by
  classical
  unfold wordCount
  exact Finset.card_equiv e (by intro r; simp [PowIndex.get_reindex])

private abbrev ExactBlock (ell : ℕ) (beta : Profile ell) (N : ℕ) :=
  {w : PowIndex (CompleteWord ell) N // ApproxConsistent id beta 0 w}

private noncomputable def exactAction (ell : ℕ) (beta : Profile ell) (N : ℕ) :
    MulAction (Equiv.Perm (Fin N)) (ExactBlock ell beta N) where
  smul e w := ⟨PowIndex.reindex e.symm w.1, by
    simpa only [ApproxConsistent, count_reindex] using w.2⟩
  one_smul w := by
    apply Subtype.ext
    apply (PowIndex.equivFun (CompleteWord ell) N).injective
    funext r
    change PowIndex.get N (PowIndex.reindex (1 : Equiv.Perm (Fin N)).symm w.1) r =
      PowIndex.get N w.1 r
    rw [PowIndex.get_reindex]
    rfl
  mul_smul e f w := by
    apply Subtype.ext
    apply (PowIndex.equivFun (CompleteWord ell) N).injective
    funext r
    change PowIndex.get N (PowIndex.reindex (e * f).symm w.1) r =
      PowIndex.get N (PowIndex.reindex e.symm (PowIndex.reindex f.symm w.1)) r
    simp only [PowIndex.get_reindex]
    rfl

private theorem exact_count_eq {ell N : ℕ} (beta : Profile ell)
    (w : ExactBlock ell beta N) (sigma : CompleteWord ell) :
    (wordCount id w.1 sigma : ℝ) = (N : ℝ) * beta.probability sigma := by
  have h := w.2 sigma
  have hzero : |(wordCount id w.1 sigma : ℝ) - (N : ℝ) * beta.probability sigma| = 0 :=
    le_antisymm (by simpa using h) (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

/-- Uniform shuffles on one exact complete-profile type, not an approximate union. -/
theorem solution (ell : ℕ) (beta : Profile ell) (N : ℕ) :
    ∃ system : AvailableBlockShuffle
      {w : PowIndex (CompleteWord ell) N // ApproxConsistent id beta 0 w}
      (Equiv.Perm (Fin N)),
      ∀ e source, (system.move e source).1 = PowIndex.reindex e.symm source.1 := by
  classical
  letI := exactAction ell beta N
  have htrans : MulAction.IsPretransitive (Equiv.Perm (Fin N))
      (ExactBlock ell beta N) := by
    constructor
    intro source target
    let f := PowIndex.get N source.1
    let g := PowIndex.get N target.1
    have hcard (sigma : CompleteWord ell) :
        Fintype.card {r : Fin N // f r = sigma} =
          Fintype.card {r : Fin N // g r = sigma} := by
      have hcounts : wordCount id source.1 sigma = wordCount id target.1 sigma := by
        exact_mod_cast (exact_count_eq beta source sigma).trans
          (exact_count_eq beta target sigma).symm
      simpa only [Fintype.card_subtype, wordCount, id_eq, f, g] using hcounts
    let fiberEquiv : ∀ sigma : CompleteWord ell,
        {r : Fin N // f r = sigma} ≃ {r : Fin N // g r = sigma} :=
      fun sigma ↦ Fintype.equivOfCardEq (hcard sigma)
    let e : Equiv.Perm (Fin N) := Equiv.ofFiberEquiv fiberEquiv
    have hlabel : ∀ r, g (e r) = f r := Equiv.ofFiberEquiv_map fiberEquiv
    refine ⟨e, ?_⟩
    apply Subtype.ext
    apply (PowIndex.equivFun (CompleteWord ell) N).injective
    funext r
    change PowIndex.get N (PowIndex.reindex e.symm source.1) r = g r
    rw [PowIndex.get_reindex]
    have h := hlabel (e.symm r)
    simpa only [Equiv.apply_symm_apply] using h.symm
  letI := htrans
  obtain ⟨system, hsystem⟩ :=
    mme_dwz_available_block_shuffle_of_pretransitive_action
      (ExactBlock ell beta N) (Equiv.Perm (Fin N))
  refine ⟨system, ?_⟩
  intro e source
  exact congrArg Subtype.val (hsystem e source)
