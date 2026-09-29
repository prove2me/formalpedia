-- Prove2me | Definitions.Def_mme_global_CW_histogram_frame
-- name    : mme_global_CW_histogram_frame
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-22T10:23:41.921769+00:00
-- url     : https://prove2.me/theorems/c0b6e692-5588-47a1-8fff-34ca43fd8fe0
-- title:
--   Coarse global histogram frames and canonical counted stages
-- statement:
--   Stores only the coarse address and original block positions; defines admissible exact histograms, general histogram windows, and a counted stage with canonical valid repair exponent. No prime, hash-incidence estimate, exact-type cover or tensor restriction is assumed.
-- source:
--   Original unpaired global stage for More Asymmetry Theorem 5.3.

import Definitions.Def_mme_global_CW_counted_stage
import Mathlib.Data.Nat.Log
open BigOperators MME MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
namespace MME.GlobalCW

/-- Coarse global data before selecting complete-word histograms or repair parameters.
The positions are original blocks, with no paired-parent constraint. -/
structure HistogramFrame (ell M : ℕ) where
  degree : ℕ
  R : ℕ
  bounds : Fin R → Fin 3 → ℕ
  n : Fin R → ℕ
  m : ∀ r, RecursiveThinSplit.Split degree (bounds r) → ℕ
  N : ℕ
  hashPositions : Fin (N+1) ≃ Place n
  degree_eq : degree = 2 * 2 ^ (ell-1)
  L : ℕ
  positions : Fin L ≃ Place n
  length : L * 2 ^ (ell-1) = M
  reference : RecursiveXHash.Address degree R bounds n
  reference_target : reference ∈ RecursiveXHash.target m

abbrev HistogramFrame.Profile {ell M : ℕ} (D : HistogramFrame ell M) :=
  Fin 3 → Cell D.degree D.R D.bounds → CompleteWord ell → ℕ

def HistogramFrame.Admissible {ell M : ℕ} (D : HistogramFrame ell M) (mu : D.Profile) : Prop :=
  (∀ i c, ∑ w, mu i c w = D.m c.1 c.2) ∧
  (∀ i c w, 0 < mu i c w → CWCells.grade w = (c.2.val i).val) ∧
  BoundaryProfiles mu

abbrev HistogramFrame.AdmissibleProfile {ell M : ℕ} (D : HistogramFrame ell M) :=
  {mu : D.Profile // D.Admissible mu}

noncomputable def HistogramFrame.capacity {ell M : ℕ} (D : HistogramFrame ell M)
    (mu : D.Profile) : ℕ :=
  ∏ i : Fin 3, Nat.card (CWCells.Block ell (cell D.reference)
    (fun c i ↦ (c.2.val i).val) mu i)

/-- Canonical repair exponent, valid for every repair scale greater than one. -/
noncomputable def HistogramFrame.stage {ell M : ℕ} (D : HistogramFrame ell M)
    (mu : D.AdmissibleProfile) (d : ℕ) (hd : 1 < d) : CountedStage ell M where
  degree := D.degree
  R := D.R
  bounds := D.bounds
  n := D.n
  m := D.m
  N := D.N
  hashPositions := D.hashPositions
  degree_eq := D.degree_eq
  L := D.L
  positions := D.positions
  length := D.length
  mu := mu.val
  mass := mu.property.1
  boundary := mu.property.2.2
  reference := D.reference
  reference_target := D.reference_target
  repairScale := d
  repairExponent := Nat.log d (D.capacity mu.val) + 1
  capacity := Nat.lt_pow_succ_log_self hd _

/-- Any condition on the exact mode histograms, including a tolerance window. -/
def HistogramFrame.window {ell M : ℕ} (D : HistogramFrame ell M)
    (good : Fin 3 → (Cell D.degree D.R D.bounds → CompleteWord ell → ℕ) → Prop) :
    ProfiledCW.Predicate M :=
  fun i x ↦ Graded i D.reference (ProfiledCW.split D.positions D.length x) ∧
    good i (count (cell D.reference) (ProfiledCW.split D.positions D.length x))

end MME.GlobalCW


