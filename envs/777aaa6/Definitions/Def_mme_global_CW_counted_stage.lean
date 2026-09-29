-- Prove2me | Definitions.Def_mme_global_CW_counted_stage
-- name    : mme_global_CW_counted_stage
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-22T07:54:22.869006+00:00
-- url     : https://prove2.me/theorems/dd8c3bab-3dae-4e9c-b033-6fc6488fccd5
-- title:
--   Pre-hash global stage and explicit counting scale
-- statement:
--   Global profiles, exact cell masses, a target reference and a repair capacity determine three finite counting loads, their common maximum scale and an explicit logarithmic copy bound. No prime, AP-free label set, usable-state incidence estimate, hole bound or tensor restriction is assumed.
-- source:
--   More Asymmetry Proposition 5.1 / Theorem 5.3: finite global extraction interface.

import Definitions.Def_mme_global_CW_counting_data
import Definitions.Def_mme_common_hash_scale
open BigOperators MME MME.RecursiveYZ MME.GlobalCW
open scoped Classical
set_option autoImplicit false
namespace MME.GlobalCW

/-- Pre-hash global data. It stores profiles and a finite repair capacity, but
neither a prime, usable states, a hash-incidence bound, nor a tensor restriction. -/
structure CountedStage (ell M : ℕ) where
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
  mu : Fin 3 → Cell degree R bounds → CompleteSplit.CompleteWord ell → ℕ
  mass : ∀ i c, ∑ w, mu i c w = m c.1 c.2
  boundary : BoundaryProfiles mu
  reference : RecursiveXHash.Address degree R bounds n
  reference_target : reference ∈ RecursiveXHash.target m
  repairScale : ℕ
  repairExponent : ℕ
  capacity : (∏ i : Fin 3, Nat.card (CWCells.Block ell (cell reference)
    (fun c i ↦ (c.2.val i).val) mu i)) < repairScale ^ repairExponent

noncomputable def CountedStage.fiberMax {ell M : ℕ} (D : CountedStage ell M) (i : Fin 3) : ℕ :=
  (RecursiveXHash.target (n := D.n) D.m).sup (fun a ↦
    ((RecursiveXHash.target (n := D.n) D.m).filter
      (fun b ↦ RecursiveXHash.block i b = RecursiveXHash.block i a)).card)

noncomputable def CountedStage.num {ell M : ℕ} (D : CountedStage ell M) : Fin 3 → ℕ :=
  ![8 * (RecursiveXHash.ambient (n := D.n) D.m).card,
    128 * D.repairScale * D.fiberMax 1 * compatibilityNumber yBoundary (modeGroup 1) (D.mu 1),
    128 * D.repairScale * D.fiberMax 2 * compatibilityNumber zBoundary (modeGroup 2) (D.mu 2)]

noncomputable def CountedStage.den {ell M : ℕ} (D : CountedStage ell M) : Fin 3 → ℕ :=
  ![((RecursiveXHash.ambient (n := D.n) D.m).image (RecursiveXHash.block 0)).card,
    modeNumber 1 (D.mu 1), modeNumber 2 (D.mu 2)]

noncomputable def CountedStage.scale {ell M : ℕ} (D : CountedStage ell M) : ℕ :=
  RegionRealization.commonScale D.degree D.num D.den

noncomputable def CountedStage.lower {ell M : ℕ} (D : CountedStage ell M) : ℝ :=
  (RecursiveXHash.target (n := D.n) D.m).card *
    Real.exp (-4 * Real.sqrt (Real.log D.scale)) / (32 * D.scale)

noncomputable def CountedStage.certifiedLogCopies {ell M : ℕ} (D : CountedStage ell M) : ℝ :=
  Real.log (RecursiveXHash.target (n := D.n) D.m).card -
    4 * Real.sqrt (Real.log D.scale) - Real.log (64 * (D.scale : ℝ)) -
      D.repairExponent * Real.log 8

noncomputable def CountedStage.output {ell M : ℕ} (D : CountedStage ell M) : ProfiledCW.Predicate M :=
  fun i x ↦ Graded i D.reference (ProfiledCW.split D.positions D.length x) ∧
    Useful (cell D.reference) (D.mu i) (ProfiledCW.split D.positions D.length x)
end MME.GlobalCW


