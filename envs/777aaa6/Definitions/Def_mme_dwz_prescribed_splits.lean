-- Prove2me | Definitions.Def_mme_dwz_prescribed_splits
-- name    : mme_dwz_prescribed_splits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-25T11:05:20.226108+00:00
-- url     : https://prove2.me/theorems/809bce54-0033-4770-b309-e7922d258587
-- title:
--   Finite prescribed split words on disjoint position cells
-- statement:
--   For a finite position set S and a list of natural counts, `PrescribedSplits S counts` is the type of sequential choices of pairwise-disjoint, ordered cells of those sizes. If the counts sum to |S|, the cells exhaust S and therefore encode exactly a split word with the prescribed symbol multiplicities. The definition supplies canonical finiteness instances so exact cardinalities can be stated with `Nat.card`.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Section 6.2, Lemma 6.7 numerator count immediately before Equation (23), printed p. 55 (PDF p. 56).

import Mathlib

set_option autoImplicit false

universe u

namespace MME.DWZCompatibilityCount

/-- Sequential choices of disjoint labelled cells of prescribed sizes inside `S`. When the sizes sum to `S.card`, this is an ordered partition of all of `S`. -/
def PrescribedSplits {ι : Type u} [DecidableEq ι] (S : Finset ι) : List ℕ → Type u
  | [] => PUnit
  | c :: cs => Σ T : ↥(S.powersetCard c), PrescribedSplits (S \ (T : Finset ι)) cs

noncomputable def prescribedSplitsFintype {ι : Type u} [DecidableEq ι] (S : Finset ι) :
    ∀ cs : List ℕ, Fintype (PrescribedSplits S cs)
  | [] => by
      simp only [PrescribedSplits]
      infer_instance
  | c :: cs => by
      simp only [PrescribedSplits]
      letI (T : ↥(S.powersetCard c)) :=
        prescribedSplitsFintype (S \ (T : Finset ι)) cs
      infer_instance

noncomputable instance prescribedSplitsFinite {ι : Type u} [DecidableEq ι]
    (S : Finset ι) (cs : List ℕ) : Finite (PrescribedSplits S cs) := by
  letI := prescribedSplitsFintype S cs
  infer_instance

end MME.DWZCompatibilityCount


