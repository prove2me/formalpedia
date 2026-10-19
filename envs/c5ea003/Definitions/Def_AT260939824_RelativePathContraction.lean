-- Prove2me | Definitions.Def_AT260939824_RelativePathContraction
-- name    : AT260939824_RelativePathContraction
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:43:31.532964+00:00
-- url     : https://prove2.me/theorems/adfe020a-1810-4fbd-afa7-d355cb9c8737
-- title:
--   Controlled contractions and the four-stage relative path homotopy
-- statement:
--   For a metric space $Z$, $p\in Z$, and $D,J\ge0$, a controlled contraction is a continuous map $H:Z\times I\to Z$, $I=[0,1]$, satisfying
--   $$H(z,0)=z,\quad H(z,1)=p,\quad H(p,t)=p,$$
--   with each time track $D$-Lipschitz and the whole map $J$-Lipschitz for the maximum product metric. Its reversed track gives a short path $t\mapsto H(q,1-t)$ from $p$ to $q$. For every path $P:p\to q$, the relative homotopy to this short path is defined in four stages: compress $P$ into the first third, insert a contraction spur at $q$, slide the contracted intermediate point along $P$, and expand the remaining reversed contraction track. All stages use clamped affine time parameters and preserve both endpoints, with the starting path retaining its original parametrization.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/RelativePathContraction.lean, selected declaration lines 20, 22-23, 25-26, 28-29, 31-32, 34-35, 37-38, 40-41, 43-53, 55-56, 58-66, 68-76, 83-87, 89, 91-92, 94-95, 97-98, 100-105, 107-113, 115-135, 137-140, 142-156, 158-161, 163-173, 175-176, 178-179, 181-182, 184-185, 187-191, 193-199, 201-208, 210-212, 214-224, 226-237, 239-251, 253, 255, 257-258, 260-261, 263-264, 266-267, 269-274, 276-299, 301-305; SHA-256 8ea4bdbcdc5fd7032e2306fff9fe6f94176fcd0c9d851bfbd370476c9ab7151e. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Init
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

/-!
# Relative path contraction

The four stages of Lemma 5.1 in arXiv:2609.39824. The contraction
is an explicit input; existence of the finite carriers is separate.
-/

namespace AbelianTargets

open scoped unitInterval NNReal
open Set

noncomputable section

def clampInterval : ℝ → I := Set.projIcc 0 1 zero_le_one

@[simp] theorem clampInterval_zero : clampInterval 0 = 0 := by
  apply Subtype.ext; simp [clampInterval, Set.projIcc]

@[simp] theorem clampInterval_one : clampInterval 1 = 1 := by
  apply Subtype.ext; simp [clampInterval, Set.projIcc]

@[simp] theorem clampInterval_coe (t : I) : clampInterval (t : ℝ) = t :=
  Subtype.ext (by simp [clampInterval, Set.projIcc, t.property.1, t.property.2])

theorem continuous_clampInterval : Continuous clampInterval :=
  (LipschitzWith.projIcc zero_le_one).continuous

theorem lipschitz_clampInterval : LipschitzWith 1 clampInterval :=
  LipschitzWith.projIcc zero_le_one

theorem clampInterval_of_nonpos {r : ℝ} (hr : r ≤ 0) : clampInterval r = 0 :=
  Set.projIcc_of_le_left zero_le_one hr

theorem clampInterval_of_one_le {r : ℝ} (hr : 1 ≤ r) : clampInterval r = 1 :=
  Set.projIcc_of_right_le zero_le_one hr

theorem clampInterval_symm (r : ℝ) : unitInterval.symm (clampInterval r) = clampInterval (1-r) := by
  by_cases hr0 : r ≤ 0
  · rw [clampInterval_of_nonpos hr0, clampInterval_of_one_le (by linarith)]
    simp
  by_cases hr1 : 1 ≤ r
  · rw [clampInterval_of_one_le hr1, clampInterval_of_nonpos (by linarith)]
    simp
  apply Subtype.ext
  simp only [unitInterval.coe_symm_eq, clampInterval, Set.coe_projIcc]
  rw [min_eq_right (by linarith : r ≤ 1), max_eq_right (by linarith : 0 ≤ r),
    min_eq_right (by linarith : 1-r ≤ 1), max_eq_right (by linarith : 0 ≤ 1-r)]

def slot3 {A B : Type*} (f g h : A × ℝ → B) (z : A × ℝ) : B :=
  if z.2 ≤ (1/3 : ℝ) then f z else if z.2 ≤ (2/3 : ℝ) then g z else h z

theorem continuous_slot3 {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f g h : A × ℝ → B) (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hfg : ∀ a, f (a,1/3) = g (a,1/3)) (hgh : ∀ a, g (a,2/3) = h (a,2/3)) :
    Continuous (slot3 f g h) := by
  have hinner : Continuous (fun z : A × ℝ => if z.2 ≤ (2/3 : ℝ) then g z else h z) :=
    continuous_if_le continuous_snd continuous_const hg.continuousOn hh.continuousOn
      (fun z hz => by rcases z with ⟨a,u⟩; dsimp at hz; subst u; exact hgh a)
  exact continuous_if_le continuous_snd continuous_const hf.continuousOn hinner.continuousOn
    (fun z hz => by rcases z with ⟨a,u⟩; dsimp at hz; subst u; dsimp; rw [if_pos (by norm_num)]; exact hfg a)

structure ControlledContraction {Z : Type*} [MetricSpace Z] (p : Z)
    (D J : ℝ≥0) where
  map : Z × I → Z
  continuous : Continuous map
  at_zero : ∀ z, map (z,0) = z
  at_one : ∀ z, map (z,1) = p
  fixes : ∀ t, map (p,t) = p
  track : ∀ z, LipschitzWith D (fun t => map (z,t))
  joint : LipschitzWith J map

namespace ControlledContraction

variable {Z : Type*} [MetricSpace Z] {p q : Z} {D J : ℝ≥0}
variable (H : ControlledContraction p D J)

def shortPath (q : Z) : Path p q where
  toFun t := H.map (q,unitInterval.symm t)
  continuous_toFun := H.continuous.comp (continuous_const.prodMk unitInterval.continuous_symm)
  source' := by simpa using H.at_one q
  target' := by simpa using H.at_zero q

def compressionWidth (s : I) : ℝ := 1 - (2/3 : ℝ) * s

theorem compressionWidth_ge (s : I) : (1/3 : ℝ) ≤ compressionWidth s := by
  unfold compressionWidth; have := s.property.2; linarith

theorem compressionWidth_pos (s : I) : 0 < compressionWidth s :=
  lt_of_lt_of_le (by norm_num) (compressionWidth_ge s)

def compressRaw (P : Path p q) (z : I × ℝ) : Z :=
  P (clampInterval (z.2 / compressionWidth z.1))

theorem continuous_compressRaw (P : Path p q) : Continuous (compressRaw P) := by
  apply P.continuous.comp
  apply continuous_clampInterval.comp
  exact continuous_snd.div (continuous_const.sub (continuous_const.mul
    (continuous_subtype_val.comp continuous_fst)))
    (fun z => ne_of_gt (compressionWidth_pos z.1))

def compressedPath (P : Path p q) : Path p q where
  toFun u := P (clampInterval (3 * (u : ℝ)))
  continuous_toFun := P.continuous.comp (continuous_clampInterval.comp (by fun_prop))
  source' := by simp
  target' := by
    have hc : clampInterval 3 = (1 : I) := Set.projIcc_of_right_le zero_le_one (by norm_num)
    simpa only [Set.Icc.coe_one, mul_one, hc] using P.target

def compressionHomotopy (P : Path p q) : P.Homotopy (compressedPath P) where
  toFun z := compressRaw P (z.1,(z.2 : ℝ))
  continuous_toFun := (continuous_compressRaw P).comp (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd))
  map_zero_left u := by simp [compressRaw, compressionWidth]
  map_one_left u := by
    simp only [compressRaw, compressionWidth, compressedPath, Set.Icc.coe_one, mul_one]
    exact congrArg (fun a : ℝ => P (clampInterval a)) (by ring)
  prop' := by
    intro s u hu
    rcases hu with rfl | hu
    · simp [compressRaw]
    · have hu : u = 1 := Set.mem_singleton_iff.mp hu
      subst u
      have hc : clampInterval (1 / compressionWidth s) = (1 : I) := by
        apply Set.projIcc_of_right_le
        have hs : compressionWidth s ≤ 1 := by
          unfold compressionWidth; have := s.property.1; linarith
        exact (one_le_div (compressionWidth_pos s)).mpr hs
      change P (clampInterval (1 / compressionWidth s)) = P 1
      rw [hc]

def spurRaw (P : Path p q) (z : I × ℝ) : Z :=
  slot3 (fun z => P (clampInterval (3*z.2)))
    (fun z => H.map (q,z.1 * clampInterval (3*z.2-1)))
    (fun z => H.map (q,z.1 * clampInterval (3-3*z.2))) z

theorem continuous_spurRaw (P : Path p q) : Continuous (H.spurRaw P) := by
  apply continuous_slot3
  · exact P.continuous.comp (continuous_clampInterval.comp (by fun_prop))
  · apply H.continuous.comp
    apply continuous_const.prodMk
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp (continuous_clampInterval.comp (by fun_prop)))
  · apply H.continuous.comp
    apply continuous_const.prodMk
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp (continuous_clampInterval.comp (by fun_prop)))
  · intro s; norm_num [H.at_zero]
  · intro s; norm_num

def thirdRaw (P : Path p q) (z : I × ℝ) : Z :=
  slot3 (fun z => P (z.1 * clampInterval (3*z.2)))
    (fun z => H.map (P z.1,clampInterval (3*z.2-1)))
    (fun z => H.map (q,clampInterval (3-3*z.2))) z

theorem continuous_thirdRaw (P : Path p q) : Continuous (H.thirdRaw P) := by
  apply continuous_slot3
  · apply P.continuous.comp
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp (continuous_clampInterval.comp (by fun_prop)))
  · exact H.continuous.comp ((P.continuous.comp continuous_fst).prodMk
      (continuous_clampInterval.comp (by fun_prop)))
  · exact H.continuous.comp (continuous_const.prodMk (continuous_clampInterval.comp (by fun_prop)))
  · intro r; norm_num [H.at_zero]
  · intro r; norm_num [H.at_one]

theorem spurRaw_source (P : Path p q) (s : I) : H.spurRaw P (s,0) = p := by
  norm_num [spurRaw, slot3]

theorem spurRaw_target (P : Path p q) (s : I) : H.spurRaw P (s,1) = q := by
  norm_num [spurRaw, slot3, H.at_zero]

theorem thirdRaw_source (P : Path p q) (r : I) : H.thirdRaw P (r,0) = p := by
  norm_num [thirdRaw, slot3]

theorem thirdRaw_target (P : Path p q) (r : I) : H.thirdRaw P (r,1) = q := by
  norm_num [thirdRaw, slot3, H.at_zero]

def spurPath (P : Path p q) : Path p q where
  toFun u := H.spurRaw P (1,(u : ℝ))
  continuous_toFun := (H.continuous_spurRaw P).comp (continuous_const.prodMk continuous_subtype_val)
  source' := H.spurRaw_source P 1
  target' := H.spurRaw_target P 1

def pausedPath (q : Z) : Path p q where
  toFun u := H.shortPath q (clampInterval (3*(u : ℝ)-2))
  continuous_toFun := (H.shortPath q).continuous.comp (continuous_clampInterval.comp (by fun_prop))
  source' := by
    rw [show clampInterval (3*(0 : I)-2) = 0 from clampInterval_of_nonpos (by norm_num)]
    exact (H.shortPath q).source
  target' := by norm_num

theorem spurRaw_zero (P : Path p q) (u : I) : H.spurRaw P (0,(u : ℝ)) = compressedPath P u := by
  have hpause (hu : ¬ (u : ℝ) ≤ 1/3) : clampInterval (3*(u : ℝ)) = 1 :=
    clampInterval_of_one_le (by linarith)
  unfold spurRaw slot3 compressedPath
  split_ifs with hu hu'
  · rfl
  · simp [H.at_zero, hpause hu]
  · simp [H.at_zero, hpause hu]

theorem thirdRaw_one (P : Path p q) (u : I) : H.thirdRaw P (1,(u : ℝ)) = H.spurPath P u := by
  simp only [thirdRaw, spurPath, spurRaw, slot3, one_mul, Path.target]
  rfl

theorem thirdRaw_zero (P : Path p q) (u : I) : H.thirdRaw P (0,(u : ℝ)) = H.pausedPath q u := by
  unfold thirdRaw slot3 pausedPath
  split_ifs with hu hu'
  · have hc : clampInterval (3*(u : ℝ)-2) = 0 := clampInterval_of_nonpos (by linarith)
    simp [hc, shortPath, H.at_one]
  · have hc : clampInterval (3*(u : ℝ)-2) = 0 := clampInterval_of_nonpos (by linarith)
    simp [hc, shortPath, H.at_one, H.fixes]
  · change H.map (q,clampInterval (3-3*(u : ℝ))) =
      H.map (q,unitInterval.symm (clampInterval (3*(u : ℝ)-2)))
    rw [clampInterval_symm]
    rw [show 1-(3*(u : ℝ)-2) = 3-3*(u : ℝ) by ring]

def spurHomotopy (P : Path p q) : (compressedPath P).Homotopy (H.spurPath P) where
  toFun z := H.spurRaw P (z.1,(z.2 : ℝ))
  continuous_toFun := (H.continuous_spurRaw P).comp (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd))
  map_zero_left := H.spurRaw_zero P
  map_one_left _ := rfl
  prop' s u hu := by
    rcases hu with rfl | hu
    · exact (H.spurRaw_source P s).trans (compressedPath P).source.symm
    · have hu : u = 1 := Set.mem_singleton_iff.mp hu
      subst u
      exact (H.spurRaw_target P s).trans (compressedPath P).target.symm

def thirdHomotopy (P : Path p q) : (H.spurPath P).Homotopy (H.pausedPath q) where
  toFun z := H.thirdRaw P (unitInterval.symm z.1,(z.2 : ℝ))
  continuous_toFun := (H.continuous_thirdRaw P).comp
    ((unitInterval.continuous_symm.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))
  map_zero_left u := by simpa using H.thirdRaw_one P u
  map_one_left u := by simpa using H.thirdRaw_zero P u
  prop' s u hu := by
    rcases hu with rfl | hu
    · exact (H.thirdRaw_source P _).trans (H.spurPath P).source.symm
    · have hu : u = 1 := Set.mem_singleton_iff.mp hu
      subst u
      exact (H.thirdRaw_target P _).trans (H.spurPath P).target.symm

def pauseWidth (s : I) : ℝ := (2/3 : ℝ) * (1-s)

def expansionWidth (s : I) : ℝ := 1-pauseWidth s

theorem pauseWidth_nonneg (s : I) : 0 ≤ pauseWidth s := by
  unfold pauseWidth; have := s.property.2; positivity

theorem expansionWidth_ge (s : I) : (1/3 : ℝ) ≤ expansionWidth s := by
  unfold expansionWidth pauseWidth; have := s.property.1; linarith

theorem expansionWidth_pos (s : I) : 0 < expansionWidth s :=
  lt_of_lt_of_le (by norm_num) (expansionWidth_ge s)

def expandRaw (q : Z) (z : I × ℝ) : Z :=
  H.shortPath q (clampInterval ((z.2-pauseWidth z.1)/expansionWidth z.1))

theorem continuous_expandRaw (q : Z) : Continuous (H.expandRaw q) := by
  apply (H.shortPath q).continuous.comp
  apply continuous_clampInterval.comp
  have hβ : Continuous (fun z : I × ℝ => pauseWidth z.1) := by unfold pauseWidth; fun_prop
  exact (continuous_snd.sub hβ).div (continuous_const.sub hβ)
    (fun z => ne_of_gt (expansionWidth_pos z.1))

def expansionHomotopy (q : Z) : (H.pausedPath q).Homotopy (H.shortPath q) where
  toFun z := H.expandRaw q (z.1,(z.2 : ℝ))
  continuous_toFun := (H.continuous_expandRaw q).comp (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd))
  map_zero_left u := by
    change H.shortPath q (clampInterval (((u : ℝ)-pauseWidth 0)/expansionWidth 0)) =
      H.shortPath q (clampInterval (3*(u : ℝ)-2))
    congr 2
    dsimp [pauseWidth, expansionWidth]
    ring
  map_one_left u := by simp [expandRaw, pauseWidth, expansionWidth]
  prop' s u hu := by
    rcases hu with rfl | hu
    · have hc : clampInterval ((0-pauseWidth s)/expansionWidth s) = 0 :=
        clampInterval_of_nonpos (div_nonpos_of_nonpos_of_nonneg
          (by have := pauseWidth_nonneg s; linarith) (expansionWidth_pos s).le)
      change H.shortPath q (clampInterval ((0-pauseWidth s)/expansionWidth s)) = H.pausedPath q 0
      rw [hc]
      exact (H.shortPath q).source.trans (H.pausedPath q).source.symm
    · have hu : u = 1 := Set.mem_singleton_iff.mp hu
      subst u
      change H.shortPath q (clampInterval ((1-pauseWidth s)/expansionWidth s)) = H.pausedPath q 1
      rw [show 1-pauseWidth s = expansionWidth s from rfl, div_self (ne_of_gt (expansionWidth_pos s)), clampInterval_one]
      exact (H.shortPath q).target.trans (H.pausedPath q).target.symm

/-- The exact endpoint-preserving four-stage construction. Its starting
path is the given path with its original parametrization. -/
def relativeHomotopy (P : Path p q) : P.Homotopy (H.shortPath q) :=
  ((compressionHomotopy P).trans (H.spurHomotopy P)).trans
    ((H.thirdHomotopy P).trans (H.expansionHomotopy q))

end ControlledContraction
end
end AbelianTargets


