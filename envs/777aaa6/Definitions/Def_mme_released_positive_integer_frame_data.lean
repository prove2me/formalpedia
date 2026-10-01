-- Prove2me | Definitions.Def_mme_released_positive_integer_frame_data
-- name    : mme_released_positive_integer_frame_data
-- status  : Definition
-- author  : @BrunoDCDO
-- created : 2026-09-24T02:22:43.373099+00:00
-- url     : https://prove2.me/theorems/c931a3dd-5756-487f-9bc2-693b71748249
-- title:
--   Positive integer frames for the compact released regions
-- statement:
--   A positive integer frame stores the finite geometry and exact integer constraints for one released compact region at scale $k$. Let $D=10^{12}$ and let $B$ be that common region's number of parent occurrences. The parent grades and the three integer-count families are fixed to the published compact data:
--
--   $$
--   p=p_3,\qquad n=k n_3,\qquad m=k m_3,\qquad \mu=k\mu_3.
--   $$
--
--   The frame stores an enumeration of the parent occurrences, an enumeration of their two child positions, and one reference address realizing the split counts $m$. It records exact child masses, grade support, the three boundary-reflection identities, the bound $kD^2\le n(r)$ for every compact label, and divisibility $kD^2\mid m(r,c)$. The physical enumeration identifies parent grading and every positive-tolerance parent band with the canonical common-coordinate predicates on the same fine word.
--
--   The transparent constructor keeps these data unchanged. Given $k>0$, a repair scale $d>1$, a tolerance $\varepsilon>0$, and
--
--   $$
--   8d\cdot25\cdot88\cdot9^2\le kD^2\varepsilon^2,
--   $$
--
--   it builds an ordinary `IntegerStep` at level two on the canonical common parent band of radius $\varepsilon$. Its minimum is $kD^2$, its repair scale is $d$, and it uses the frame's same reference and positions. Existence of a frame is a separate theorem. This definition supplies no output-rate budget, nearby-profile coverage, or recursive matrix-multiplication construction.
-- source:
--   Finite-data assembly interface for the published RecStage tables (p2m:theorem/60610bd3-0675-4be4-a731-ca71c173a5bc, marwahaha), common profiles and position frame (p2m:theorem/3d489536-019f-46c1-b6c3-52ee24f948d0 and p2m:theorem/8bcbc67f-e01e-4bd0-ad82-deb2f4e5b904, Robertboy18), and released exact seed (p2m:theorem/cb80ec03-0b0a-4b6c-a75e-ca788b94d914, raresbuhai). Underlying regional construction: Alman, Duan, Vassilevska Williams, Xu, Xu and Zhou, More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/pdf/2404.16349v2, Section 6.1 and Claim 6.5, printed page 32. This interface is not stated verbatim in the paper; its nontrivial existence is a separate theorem.

import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_released_joint_interior_frame
import Definitions.Def_mme_graded_integer_regional_step_data
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open scoped BigOperators
open MME MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.MoreAsymmetryExactSeed

namespace MME.ReleasedPositiveInteger

/-- Integer geometry over abstract profiles. Keeping these functions as
parameters avoids generating record eliminators over the released tables. -/
structure FrameData {half ell R M B L : ℕ}
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (total : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ)
    (length : L * 2 ^ (ell - 1) = M) (minimum : ℕ)
    (grading : ProfiledCW.Predicate M) (source : ℝ → ProfiledCW.Predicate M) where
  hashPositions : Fin (B - 1 + 1) ≃ (r : Fin R) × Fin (n r)
  positions : Fin L ≃ Position n
  reference : RecursiveXHash.Address half R parent n
  reference_target : reference ∈ RecursiveXHash.target m
  mass : ∀ i c, (∑ w, mu i c w) = m c.1 c.2 + m c.1 (complement (total c.1) c.2)
  support : ∀ i c w, 0 < mu i c w →
    ∑ h, (w h).val = (c.2.val i).val
  boundary : BoundaryProfiles mu
  parent_size : ∀ r, minimum ≤ n r
  split_divisible : ∀ r c, minimum ∣ m r c
  parent_graded : ∀ i x,
    ParentGraded parent n i (ProfiledCW.split positions length x) ↔ grading i x
  typical : ∀ (eta : ℝ), 0 < eta → ∀ i x,
    parentTypical total n m (mu i) eta (ProfiledCW.split positions length x) ↔ source eta i x

/-- Construct an integer step without changing the finite geometry. -/
noncomputable def FrameData.step {half ell R M B L : ℕ}
    {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    {total : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half}
    {m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ}
    {mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ}
    {length : L * 2 ^ (ell - 1) = M} {minimum : ℕ}
    {grading : ProfiledCW.Predicate M} {source : ℝ → ProfiledCW.Predicate M}
    (frame : FrameData (B := B) parent n total m mu length minimum grading source)
    (half_eq : half = 2 * 2 ^ (ell - 1)) (minimum_pos : 0 < minimum)
    (repairScale : ℕ) (hrepair : 1 < repairScale)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hsize : (8 * repairScale : ℝ) *
      (25 * R * (Fintype.card (CompleteWord ell) : ℝ) ^ 2) ≤
        (minimum : ℝ) * epsilon ^ 2) : IntegerStep ell M (source epsilon) where
  half := half
  R := R
  parent := parent
  n := n
  total := total
  half_eq := half_eq
  m := m
  N := B - 1
  hashPositions := frame.hashPositions
  L := L
  positions := frame.positions
  length := length
  mu := mu
  mass := frame.mass
  support := frame.support
  boundary := frame.boundary
  reference := frame.reference
  reference_target := frame.reference_target
  minimum := minimum
  repairScale := repairScale
  minimum_pos := minimum_pos
  repairScale_gt_one := hrepair
  parent_size := frame.parent_size
  split_divisible := frame.split_divisible
  epsilon := epsilon
  epsilon_pos := hepsilon
  size_test := hsize
  source_inside := fun i x hx => (frame.typical epsilon hepsilon i x).mp hx

/-- The compact released specialization keeps all data functions literal.
Its reference is fixed across every step constructed from the frame. -/
abbrev Frame (region : Fin 6) (k : ℕ) :=
  FrameData (half := 4) (ell := 2) (R := 88)
    (M := ReleasedJointInterior.blocks region k * 4)
    (B := ReleasedJointInterior.blocks region k)
    (L := ReleasedJointInterior.blocks region k * 2)
    (RecStage.parent3 region) (fun r => k * RecStage.n3 region r) (RecStage.htotal3 region)
    (fun r c => k * RecStage.m3 region r c) (fun i c w => k * RecStage.mu3 region i c w)
    (ReleasedJointInterior.positions_length region k) (k * denominator ^ 2)
    (fun i x => ParentGraded (ReleasedJointInterior.parent region)
      (ReleasedJointInterior.size region k) i
      (ProfiledCW.split (ell := 2) (ReleasedJointInterior.positions region k)
        (ReleasedJointInterior.positions_length region k) x))
    (ReleasedJointInterior.source region k)

/-- Construct the central integer step with its geometry and profiles unchanged.
The scalar size test is explicit; no copy-rate bound is assumed. -/
noncomputable def Frame.step {region : Fin 6} {k : ℕ}
    (frame : Frame region k) (hk : 0 < k)
    (repairScale : ℕ) (hrepair : 1 < repairScale)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hsize : (8 * repairScale : ℝ) *
      (25 * 88 * (Fintype.card (CompleteWord 2) : ℝ) ^ 2) ≤
        (k * denominator ^ 2 : ℕ) * epsilon ^ 2) :
    IntegerStep 2 (ReleasedJointInterior.blocks region k * 4)
      (ReleasedJointInterior.source region k epsilon) :=
  FrameData.step frame (by norm_num) (Nat.mul_pos hk (by norm_num [denominator]))
    repairScale hrepair epsilon hepsilon hsize

end MME.ReleasedPositiveInteger


