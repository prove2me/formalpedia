-- Prove2me | solution 1 for mme_complete_split_exact_power_restrict_prescribedZPower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T06:34:07.638213+00:00
-- url     : https://prove2.me/submissions/1b8e7ef7-37db-4dfc-ab68-2a7386e4af62

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_basis_z_allowed_projection
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_TypeGrading_kron
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open MME MME.TensorObj MME.CompleteSplit MME.DWZComponentRestriction
  MME.DWZRestrictedValue PiTensorProduct Module
open scoped BigOperators Classical

universe u v

set_option autoImplicit false
set_option warningAsError true

private theorem exact_profile_split_counts
    {I : Type u} {J : Type v} [DecidableEq J] {ell N : ℕ}
    (label : I → CompleteWord ell)
    (beta : Profile ell) (split : CompleteWord ell → J)
    (counts : J → ℕ)
    (hcounts : ∀ a, (counts a : ℝ) = (N : ℝ) *
      ∑ sigma ∈ Finset.univ.filter (fun sigma ↦ split sigma = a), beta.probability sigma)
    (w : PowIndex I N) (hw : ApproxConsistent label beta 0 w) :
    ∀ a : J,
      Fintype.card {r : Fin N // split (label (PowIndex.get N w r)) = a} = counts a := by
  classical
  have hfull : ∀ sigma, (wordCount label w sigma : ℝ) = N * beta.probability sigma := by
    simpa only [ApproxConsistent, NNReal.coe_zero, mul_zero, abs_nonpos_iff,
      sub_eq_zero] using hw
  intro a
  have hsum :
      ∑ sigma ∈ Finset.univ.filter (fun sigma ↦ split sigma = a),
        wordCount label w sigma =
      Fintype.card {r : Fin N // split (label (PowIndex.get N w r)) = a} := by
    simpa only [wordCount, Fintype.card_subtype, Finset.mem_filter,
      Finset.mem_univ, true_and] using
      Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin N))
        (Finset.univ.filter (fun sigma : CompleteWord ell ↦ split sigma = a))
        (fun r ↦ label (PowIndex.get N w r))
  have hreal :
      (Fintype.card {r : Fin N // split (label (PowIndex.get N w r)) = a} : ℝ) =
      counts a := by
    calc
      _ = ∑ sigma ∈ Finset.univ.filter (fun sigma ↦ split sigma = a),
          (wordCount label w sigma : ℝ) := by exact_mod_cast hsum.symm
      _ = ∑ sigma ∈ Finset.univ.filter (fun sigma ↦ split sigma = a),
          (N : ℝ) * beta.probability sigma := by
        apply Finset.sum_congr rfl
        intro sigma hsigma
        exact hfull sigma
      _ = (N : ℝ) * ∑ sigma ∈ Finset.univ.filter (fun sigma ↦ split sigma = a),
          beta.probability sigma := (Finset.mul_sum _ _ _).symm
      _ = _ := (hcounts a).symm
  exact_mod_cast hreal

/-- An exact all-mode complete-profile power is obtained from its literal
prescribed-Z power whenever the supplied integer split counts agree with
the exact pushforward profile. -/
private theorem exact_power_restrict_split_counts
    {K : Type u} [Field K] (T : TensorObj K 3) {I : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i)) {ell : ℕ}
    (label : ∀ i, I i → CompleteWord ell) (beta : Fin 3 → Profile ell)
    (N : ℕ) {J : Type v} [DecidableEq J]
    (split : CompleteWord ell → J) (counts : J → ℕ)
    (hcounts : ∀ a, (counts a : ℝ) = (N : ℝ) *
      ∑ sigma ∈ Finset.univ.filter (fun sigma ↦ split sigma = a),
        (beta 2).probability sigma) :
    TensorObj.Restrict (restrictedPower T b label beta 0 N)
      ((T.kronPow N).basisZAllowedSubtensor (kronPowModeBasis T 2 (b 2) N)
        (fun w ↦ ∀ a : J,
          Fintype.card {r : Fin N // split (label 2 (PowIndex.get N w r)) = a} =
            counts a)) := by
  classical
  let G := (T.kronPow N).basisAllAllowedGrading
    (fun i ↦ kronPowModeBasis T i (b i) N)
    (fun i ↦ ApproxConsistent (label i) (beta i) 0)
  apply mme_restrict_basisZAllowedSubtensor_of_vanishes (T.kronPow N)
    (restrictedPower T b label beta 0 N) (kronPowModeBasis T 2 (b 2) N)
    (fun w ↦ ∀ a : J,
      Fintype.card {r : Fin N // split (label 2 (PowIndex.get N w r)) = a} = counts a)
    (fun i ↦ G.blockProj i 0) rfl
  intro w hbad
  have hnot : ¬ ApproxConsistent (label 2) (beta 2) 0 w := by
    intro hw
    exact hbad (exact_profile_split_counts (label 2) (beta 2) split counts hcounts w hw)
  have hmem : kronPowModeBasis T 2 (b 2) N w ∈ G.classOf 2 1 := by
    change kronPowModeBasis T 2 (b 2) N w ∈ Submodule.span K
      ((kronPowModeBasis T 2 (b 2) N) ''
        {w | (if ApproxConsistent (label 2) (beta 2) 0 w then (0 : Fin 2) else 1) = 1})
    exact Submodule.subset_span ⟨w, by simp [hnot], rfl⟩
  exact TensorObj.TypeGrading.blockProj_apply_mem_ne G 2 0 1 (by decide)
    (kronPowModeBasis T 2 (b 2) N w) hmem

/-- Exact complete-profile powers give a literal input to DWZ's prescribed-Z
value-pair API at every compatible integer-profile length. -/
theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) {I : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i)) {ell : ℕ}
    (label : ∀ i, I i → CompleteWord ell) (beta : Fin 3 → Profile ell)
    {t : ℕ} (split : CompleteWord ell → Fin t) (p : IntegerZSplitProfile t)
    (hprofile : ∀ a, (p.count a : ℝ) = (p.denominator : ℝ) *
      ∑ sigma ∈ Finset.univ.filter (fun sigma ↦ split sigma = a),
        (beta 2).probability sigma) (m : ℕ) :
    TensorObj.Restrict (restrictedPower T b label beta 0 (p.length m))
      (prescribedZPower T (b 2) (fun x ↦ split (label 2 x)) p m) := by
  classical
  have hcounts (a : Fin t) : ((p.count a * m : ℕ) : ℝ) = (p.length m : ℝ) *
      ∑ sigma ∈ Finset.univ.filter (fun sigma ↦ split sigma = a),
        (beta 2).probability sigma := by
    simp only [IntegerZSplitProfile.length, Nat.cast_mul]
    rw [hprofile a]
    ring
  have hallowed : prescribedZWord (fun x ↦ split (label 2 x)) p m =
      (fun w ↦ ∀ a : Fin t,
        Fintype.card {r : Fin (p.length m) //
          split (label 2 (PowIndex.get (p.length m) w r)) = a} = p.count a * m) := by
    funext w
    apply propext
    simp only [prescribedZWord, leftGradeCount, Fintype.card_subtype]
  unfold prescribedZPower
  rw [hallowed]
  exact exact_power_restrict_split_counts T b label beta (p.length m) split
    (fun a ↦ p.count a * m) hcounts
