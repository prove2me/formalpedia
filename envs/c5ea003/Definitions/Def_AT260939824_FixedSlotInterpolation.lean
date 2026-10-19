-- Prove2me | Definitions.Def_AT260939824_FixedSlotInterpolation
-- name    : AT260939824_FixedSlotInterpolation
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:45:31.203024+00:00
-- url     : https://prove2.me/theorems/bf36b3ca-6333-4543-8f84-3df4b50de4e8
-- title:
--   Affine interpolation with a common slot budget
-- statement:
--   For rows of points in a real normed space, consecutive vertices are joined affinely on equally sized parameter slots. Rows with equal endpoints interpolate through endpoint-fixed path homotopies. Convex four-corner charts keep each moving slot in its prescribed set. If the edge bound is $\Delta$, there are $n+1$ slots, and corresponding vertices move by at most $C$, the joint Lipschitz bound is $\Delta(n+1)+C$.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/FixedSlotInterpolation.lean, selected declaration lines 26-27, 29-32, 34-46, 48-56, 58-60, 62-77, 79-85, 87-93, 95-99, 101-111, 113-120, 122-133, 146-153, 155-166, 168-179, 181-189, 191-229, 231-239, 241-265, 267-269, 271-287, 289-303, 305-324, 326-334, 336-347, 349-372, 374-378, 384-385, 387-391, 393-398, 430-439, 441-454; SHA-256 e59017c49a13d04335424c6e697861f5517268f7f24c60a27c16580bc4fc3837. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_RelativePathBounds
import Definitions.Def_AT260939824_RelativePathContraction
import Init
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

/-!
# Fixed slots and the path-time estimate in Section 4

Finite rows are interpolated in fixed equal-width slots. The path-time
Lipschitz constant is simplex diameter times the slot count. It does not
depend on the number of intermediate homotopy rows. This file proves the
affine estimate and literal endpoint agreement, rather than assuming a
controlled contraction for the interval carriers.
-/

namespace AbelianTargets.FixedSlots

open scoped NNReal

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def mix (a b : E) (r : unitInterval) : E :=
  (1-(r : ℝ)) • a + (r : ℝ) • b

@[simp] theorem mix_zero (a b : E) : mix a b 0 = a := by simp [mix]
@[simp] theorem mix_one (a b : E) : mix a b 1 = b := by simp [mix]
@[simp] theorem mix_self (a : E) (r : unitInterval) : mix a a r = a := by
  simp only [mix, ← add_smul, sub_add_cancel, one_smul]

theorem mix_dist_le (a b c d : E) (r : unitInterval) :
    dist (mix a c r) (mix b d r) ≤
      (1-(r : ℝ))*dist a b + (r : ℝ)*dist c d := by
  have hnonneg : 0 ≤ 1-(r : ℝ) := sub_nonneg.mpr r.property.2
  rw [dist_eq_norm]
  have he : mix a c r - mix b d r =
      (1-(r : ℝ)) • (a-b) + (r : ℝ) • (c-d) := by
    simp only [mix, smul_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (by
    rw [norm_smul_of_nonneg hnonneg, norm_smul_of_nonneg r.property.1,
      ← dist_eq_norm, ← dist_eq_norm])

theorem mix_dist_le_of_le {a b c d : E} {Δ : ℝ}
    (hab : dist a b ≤ Δ) (hcd : dist c d ≤ Δ) (r : unitInterval) :
    dist (mix a c r) (mix b d r) ≤ Δ := by
  calc
    _ ≤ (1-(r : ℝ))*dist a b + (r : ℝ)*dist c d := mix_dist_le _ _ _ _ _
    _ ≤ (1-(r : ℝ))*Δ + (r : ℝ)*Δ :=
      add_le_add (mul_le_mul_of_nonneg_left hab (sub_nonneg.mpr r.property.2))
        (mul_le_mul_of_nonneg_left hcd r.property.1)
    _ = Δ := by ring

/-- The line in slot `j`, extended affinely outside that slot. -/
def affineSlot (T : ℕ) (row : ℕ → E) (j : ℕ) (u : ℝ) : E :=
  AffineMap.lineMap (row j) (row (j+1)) ((T : ℝ)*u-(j : ℝ))

theorem affineSlot_lipschitz (T : ℕ) (row : ℕ → E) (j : ℕ) (Δ : ℝ≥0)
    (hedge : dist (row j) (row (j+1)) ≤ Δ) :
    LipschitzWith (Δ*T) (affineSlot T row j) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  unfold affineSlot
  rw [dist_lineMap_lineMap]
  have he : dist ((T : ℝ)*u-(j : ℝ)) ((T : ℝ)*v-(j : ℝ)) =
      (T : ℝ)*dist u v := by
    rw [Real.dist_eq, show (T : ℝ)*u-(j : ℝ)-((T : ℝ)*v-(j : ℝ)) =
      (T : ℝ)*(u-v) by ring, abs_mul, abs_of_nonneg (Nat.cast_nonneg T), Real.dist_eq]
  rw [he]
  calc
    (T : ℝ)*dist u v*dist (row j) (row (j+1)) ≤ (T : ℝ)*dist u v*Δ :=
      mul_le_mul_of_nonneg_left hedge (mul_nonneg (Nat.cast_nonneg T) dist_nonneg)
    _ = (Δ*T : ℝ≥0)*dist u v := by simp; ring

theorem affineSlot_left (T : ℕ) (hT : 0 < T) (row : ℕ → E) (j : ℕ) :
    affineSlot T row j ((j : ℝ)/T) = row j := by
  unfold affineSlot
  rw [show (T : ℝ)*((j : ℝ)/T)-(j : ℝ) = 0 by
    have : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
    field_simp; ring]
  exact AffineMap.lineMap_apply_zero _ _

theorem affineSlot_right (T : ℕ) (hT : 0 < T) (row : ℕ → E) (j : ℕ) :
    affineSlot T row j (((j : ℝ)+1)/T) = row (j+1) := by
  unfold affineSlot
  rw [show (T : ℝ)*(((j : ℝ)+1)/T)-(j : ℝ) = 1 by
    have : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
    field_simp; ring]
  exact AffineMap.lineMap_apply_one _ _

/-- A finite path with one segment in each prescribed slot. -/
def rowPath (T : ℕ) (row : ℕ → E) : ℕ → ℝ → E
  | 0 => affineSlot T row 0
  | n+1 => fun u => if u ≤ ((n : ℝ)+1)/T then rowPath T row n u
      else affineSlot T row (n+1) u

theorem rowPath_right (T : ℕ) (hT : 0 < T) (row : ℕ → E) (n : ℕ) :
    rowPath T row n (((n : ℝ)+1)/T) = row (n+1) := by
  cases n with
  | zero => simpa [rowPath] using affineSlot_right T hT row 0
  | succ n =>
    change (if (((n+1 : ℕ) : ℝ)+1)/T ≤ ((n : ℝ)+1)/T then _ else _) = _
    rw [if_neg (by
      have hp : (0 : ℝ) < T := by exact_mod_cast hT
      push_cast
      exact not_le.mpr ((div_lt_div_iff_of_pos_right hp).mpr (by linarith)))]
    simpa only [Nat.cast_add, Nat.cast_one] using affineSlot_right T hT row (n+1)

theorem rowPath_zero (T : ℕ) (hT : 0 < T) (row : ℕ → E) (n : ℕ) :
    rowPath T row n 0 = row 0 := by
  induction n with
  | zero => simpa [rowPath] using affineSlot_left T hT row 0
  | succ n ih =>
    change (if (0 : ℝ) ≤ ((n : ℝ)+1)/T then _ else _) = _
    rw [if_pos (div_nonneg (by positivity) (by positivity))]
    exact ih

theorem rowPath_lipschitz (T : ℕ) (hT : 0 < T) (row : ℕ → E) (n : ℕ) (Δ : ℝ≥0)
    (hedges : ∀ j ≤ n, dist (row j) (row (j+1)) ≤ Δ) :
    LipschitzWith (Δ*T) (rowPath T row n) := by
  induction n with
  | zero => exact affineSlot_lipschitz T row 0 Δ (hedges 0 le_rfl)
  | succ n ih =>
    apply lipschitz_glue_at _ _ (ih (fun j hj => hedges j (hj.trans (Nat.le_succ n))))
      (affineSlot_lipschitz T row (n+1) Δ (hedges (n+1) le_rfl))
    rw [rowPath_right T hT row n]
    have hleft : affineSlot T row (n+1) (((n : ℝ)+1)/T) = row (n+1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using affineSlot_left T hT row (n+1)
    exact hleft.symm



theorem continuous_affineSlot {X : Type*} [TopologicalSpace X]
    (T : ℕ) (row : X → ℕ → E) (hrow : ∀ j, Continuous (fun x => row x j)) (j : ℕ) :
    Continuous (fun z : X × ℝ => affineSlot T (row z.1) j z.2) := by
  simp only [affineSlot, AffineMap.lineMap_apply_module]
  exact (continuous_const.sub (continuous_const.mul continuous_snd |>.sub continuous_const)).smul
      ((hrow j).comp continuous_fst) |>.add
    ((continuous_const.mul continuous_snd |>.sub continuous_const).smul
      ((hrow (j+1)).comp continuous_fst))

/-- Families of fixed-slot paths glue continuously at the literal row vertices. -/
theorem continuous_rowPath {X : Type*} [TopologicalSpace X]
    (T : ℕ) (hT : 0 < T) (row : X → ℕ → E)
    (hrow : ∀ j, Continuous (fun x => row x j)) (n : ℕ) :
    Continuous (fun z : X × ℝ => rowPath T (row z.1) n z.2) := by
  induction n with
  | zero => exact continuous_affineSlot T row hrow 0
  | succ n ih =>
    apply ih.if_le (continuous_affineSlot T row hrow (n+1)) continuous_snd continuous_const
    intro z hz
    rw [hz, rowPath_right T hT (row z.1) n]
    simpa only [Nat.cast_add, Nat.cast_one] using (affineSlot_left T hT (row z.1) (n+1)).symm

/-- The canonical path in `n+1` equal slots, with its exact parametrization. -/
def asPath (row : ℕ → E) (n : ℕ) : Path (row 0) (row (n+1)) where
  toFun u := rowPath (n+1) row n (u : ℝ)
  continuous_toFun := by
    have hc := continuous_rowPath (X := unitInterval) (n+1) (Nat.succ_pos n)
      (fun _ => row) (fun _ => continuous_const) n
    exact hc.comp ((continuous_const (y := (0 : unitInterval))).prodMk continuous_subtype_val)
  source' := rowPath_zero (n+1) (Nat.succ_pos n) row n
  target' := by
    have he := rowPath_right (n+1) (Nat.succ_pos n) row n
    have hne : (n : ℝ)+1 ≠ 0 := by positivity
    simpa [Nat.cast_add, Nat.cast_one, hne] using he

theorem asPath_lipschitz (row : ℕ → E) (n : ℕ) (Δ : ℝ≥0)
    (hedges : ∀ j ≤ n, dist (row j) (row (j+1)) ≤ Δ) :
    LipschitzWith (Δ*(n+1)) (asPath row n) := by
  have hv : LipschitzWith 1 (fun u : unitInterval => (u : ℝ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [NNReal.coe_one, one_mul]
    rfl
  simpa using (rowPath_lipschitz (n+1) (Nat.succ_pos n) row n Δ hedges).comp hv

/-- Interpolation between two complete rows preserves both endpoints and
the literal slot parametrizations of the initial and final rows. -/
def rowHomotopy (row₀ row₁ : ℕ → E) (n : ℕ)
    (hsource : row₀ 0 = row₁ 0) (htarget : row₀ (n+1) = row₁ (n+1)) :
    (asPath row₀ n).Homotopy ((asPath row₁ n).cast hsource htarget) where
  toFun z := rowPath (n+1) (fun j => mix (row₀ j) (row₁ j) z.1) n (z.2 : ℝ)
  continuous_toFun := by
    have hr : ∀ j, Continuous (fun r : unitInterval => mix (row₀ j) (row₁ j) r) := by
      intro j
      unfold mix
      fun_prop
    exact (continuous_rowPath (n+1) (Nat.succ_pos n) _ hr n).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  map_zero_left u := by
    change rowPath (n+1) (fun j => mix (row₀ j) (row₁ j) 0) n (u : ℝ) = _
    simp only [mix_zero]
    rfl
  map_one_left u := by
    change rowPath (n+1) (fun j => mix (row₀ j) (row₁ j) 1) n (u : ℝ) = _
    simp only [mix_one]
    rfl
  prop' r u hu := by
    rcases hu with hu | hu
    · subst u
      change rowPath (n+1) (fun j => mix (row₀ j) (row₁ j) r) n 0 = (asPath row₀ n) 0
      rw [rowPath_zero (n+1) (Nat.succ_pos n) (fun j => mix (row₀ j) (row₁ j) r) n,
        ← hsource, mix_self]
      exact (asPath row₀ n).source.symm
    · have hu' : u = 1 := Set.mem_singleton_iff.mp hu
      subst u
      have he := rowPath_right (n+1) (Nat.succ_pos n)
        (fun j => mix (row₀ j) (row₁ j) r) n
      have he' : rowPath (n+1) (fun j => mix (row₀ j) (row₁ j) r) n 1 =
          mix (row₀ (n+1)) (row₁ (n+1)) r := by
        have hne : (n : ℝ)+1 ≠ 0 := by positivity
        simpa [Nat.cast_add, Nat.cast_one, hne] using he
      change rowPath (n+1) (fun j => mix (row₀ j) (row₁ j) r) n 1 = (asPath row₀ n) 1
      rw [he', ← htarget, mix_self]
      exact (asPath row₀ n).target.symm

theorem rowHomotopy_path_time_lipschitz (row₀ row₁ : ℕ → E) (n : ℕ)
    (hsource : row₀ 0 = row₁ 0) (htarget : row₀ (n+1) = row₁ (n+1)) (Δ : ℝ≥0)
    (hedges₀ : ∀ j ≤ n, dist (row₀ j) (row₀ (j+1)) ≤ Δ)
    (hedges₁ : ∀ j ≤ n, dist (row₁ j) (row₁ (j+1)) ≤ Δ) (r : unitInterval) :
    LipschitzWith (Δ*(n+1)) ((rowHomotopy row₀ row₁ n hsource htarget).eval r) := by
  change LipschitzWith (Δ*(n+1)) (asPath (fun j => mix (row₀ j) (row₁ j) r) n)
  apply asPath_lipschitz
  intro j hj
  exact mix_dist_le_of_le (hedges₀ j hj) (hedges₁ j hj) r

theorem rowPath_on_slot (T : ℕ) (hT : 0 < T) (row : ℕ → E) (n j : ℕ)
    (hj : j ≤ n) (u : ℝ) (hu₀ : (j : ℝ)/T ≤ u) (hu₁ : u ≤ ((j : ℝ)+1)/T) :
    rowPath T row n u = affineSlot T row j u := by
  have hp : (0 : ℝ) < T := by exact_mod_cast hT
  induction n generalizing j with
  | zero =>
    have hj' : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    rfl
  | succ n ih =>
    by_cases hsmall : j ≤ n
    · have hcut : u ≤ ((n : ℝ)+1)/T := hu₁.trans
        ((div_le_div_iff_of_pos_right hp).mpr (by exact_mod_cast Nat.add_le_add_right hsmall 1))
      change (if u ≤ ((n : ℝ)+1)/T then _ else _) = _
      rw [if_pos hcut]
      exact ih j hsmall hu₀ hu₁
    · have hj' : j = n+1 := by omega
      subst j
      change (if u ≤ ((n : ℝ)+1)/T then _ else _) = _
      by_cases hcut : u ≤ ((n : ℝ)+1)/T
      · rw [if_pos hcut]
        have he : u = ((n : ℝ)+1)/T := le_antisymm hcut (by simpa using hu₀)
        rw [he, rowPath_right T hT row n]
        simpa only [Nat.cast_add, Nat.cast_one] using (affineSlot_left T hT row (n+1)).symm
      · rw [if_neg hcut]

theorem mix_mem {F : Set E} (hF : Convex ℝ F) {a b : E}
    (ha : a ∈ F) (hb : b ∈ F) (r : unitInterval) : mix a b r ∈ F := by
  exact hF ha hb (sub_nonneg.mpr r.property.2) r.property.1 (by ring)

/-- When the four slot corners lie in one convex chart, the whole moving
slot remains in that chart. This is the simplex condition in Section 4. -/
theorem interpolated_row_mem_on_slot (T : ℕ) (hT : 0 < T)
    (row₀ row₁ : ℕ → E) (n j : ℕ) (hj : j ≤ n) (r : unitInterval)
    {F : Set E} (hF : Convex ℝ F)
    (h₀₀ : row₀ j ∈ F) (h₀₁ : row₀ (j+1) ∈ F)
    (h₁₀ : row₁ j ∈ F) (h₁₁ : row₁ (j+1) ∈ F)
    (u : ℝ) (hu₀ : (j : ℝ)/T ≤ u) (hu₁ : u ≤ ((j : ℝ)+1)/T) :
    rowPath T (fun l => mix (row₀ l) (row₁ l) r) n u ∈ F := by
  rw [rowPath_on_slot T hT _ n j hj u hu₀ hu₁]
  apply hF.lineMap_mem (mix_mem hF h₀₀ h₁₀ r) (mix_mem hF h₀₁ h₁₁ r)
  have hp : (0 : ℝ) < T := by exact_mod_cast hT
  constructor
  · have he := (div_le_iff₀ hp).1 hu₀
    nlinarith
  · have he := (le_div_iff₀ hp).1 hu₁
    nlinarith

theorem affineSlot_dist_le (T : ℕ) (hT : 0 < T) (row₀ row₁ : ℕ → E) (j : ℕ)
    (u : ℝ) (hu₀ : (j : ℝ)/T ≤ u) (hu₁ : u ≤ ((j : ℝ)+1)/T)
    (C : ℝ) (hj : dist (row₀ j) (row₁ j) ≤ C)
    (hj' : dist (row₀ (j+1)) (row₁ (j+1)) ≤ C) :
    dist (affineSlot T row₀ j u) (affineSlot T row₁ j u) ≤ C := by
  have hp : (0 : ℝ) < T := by exact_mod_cast hT
  have hv : (T : ℝ)*u-(j : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · have he := (div_le_iff₀ hp).1 hu₀
      nlinarith
    · have he := (le_div_iff₀ hp).1 hu₁
      nlinarith
  let v : unitInterval := ⟨(T : ℝ)*u-(j : ℝ),hv⟩
  simpa only [affineSlot, AffineMap.lineMap_apply_module, mix] using
    mix_dist_le_of_le hj hj' v

/-- Fixed-slot interpolation is nonexpanding in the uniform distance
between the lists of row vertices. -/
theorem rowPath_dist_le (T : ℕ) (hT : 0 < T) (row₀ row₁ : ℕ → E) (n : ℕ)
    (C : ℝ) (hvertices : ∀ j ≤ n+1, dist (row₀ j) (row₁ j) ≤ C)
    (u : ℝ) (hu₀ : 0 ≤ u) (hu₁ : u ≤ ((n : ℝ)+1)/T) :
    dist (rowPath T row₀ n u) (rowPath T row₁ n u) ≤ C := by
  induction n with
  | zero =>
    apply affineSlot_dist_le T hT row₀ row₁ 0 u (by simpa using hu₀) (by simpa using hu₁)
      C (hvertices 0 (by omega)) (hvertices 1 le_rfl)
  | succ n ih =>
    change dist (if u ≤ ((n : ℝ)+1)/T then _ else _) (if u ≤ ((n : ℝ)+1)/T then _ else _) ≤ C
    by_cases hcut : u ≤ ((n : ℝ)+1)/T
    · rw [if_pos hcut, if_pos hcut]
      exact ih (fun j hj => hvertices j (hj.trans (Nat.le_succ _))) hcut
    · rw [if_neg hcut, if_neg hcut]
      apply affineSlot_dist_le T hT row₀ row₁ (n+1) u
        (by simpa only [Nat.cast_add, Nat.cast_one] using (le_of_lt (lt_of_not_ge hcut)))
        (by simpa only [Nat.cast_add, Nat.cast_one] using hu₁)
        C (hvertices (n+1) (Nat.le_succ _)) (hvertices (n+1+1) le_rfl)

theorem mix_lipschitz (a b : E) (C : ℝ≥0) (hab : dist a b ≤ C) :
    LipschitzWith C (mix a b) := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  have he : dist (mix a b r) (mix a b s) = dist r s * dist a b := by
    simpa only [mix, AffineMap.lineMap_apply_module] using
      (dist_lineMap_lineMap a b (r : ℝ) (s : ℝ))
  rw [he]
  exact (mul_le_mul_of_nonneg_left hab dist_nonneg).trans_eq (mul_comm _ _)

/-- Uniform comparison of the complete fixed-slot rows at two homotopy
parameters. Only corresponding vertex distances enter this estimate. -/
theorem interpolated_row_parameter_bound (row₀ row₁ : ℕ → E) (n : ℕ) (C : ℝ≥0)
    (hvertices : ∀ j ≤ n+1, dist (row₀ j) (row₁ j) ≤ C)
    (r s u : unitInterval) :
    dist (rowPath (n+1) (fun j => mix (row₀ j) (row₁ j) r) n (u : ℝ))
      (rowPath (n+1) (fun j => mix (row₀ j) (row₁ j) s) n (u : ℝ)) ≤ C*dist r s := by
  apply rowPath_dist_le (n+1) (Nat.succ_pos n) _ _ n (C*dist r s)
    (fun j hj => (mix_lipschitz (row₀ j) (row₁ j) C (hvertices j hj)).dist_le_mul r s)
    (u : ℝ) u.property.1
  have hne : (n : ℝ)+1 ≠ 0 := by positivity
  simpa [Nat.cast_add, Nat.cast_one, hne] using u.property.2

/-- Joint Lipschitz continuity of the actual endpoint-fixed row homotopy.
The path-time term is diameter times slot count, and the homotopy-time
term is the largest corresponding-vertex displacement. -/
theorem rowHomotopy_joint_lipschitz (row₀ row₁ : ℕ → E) (n : ℕ)
    (hsource : row₀ 0 = row₁ 0) (htarget : row₀ (n+1) = row₁ (n+1)) (Δ C : ℝ≥0)
    (hedges₀ : ∀ j ≤ n, dist (row₀ j) (row₀ (j+1)) ≤ Δ)
    (hedges₁ : ∀ j ≤ n, dist (row₁ j) (row₁ (j+1)) ≤ Δ)
    (hvertices : ∀ j ≤ n+1, dist (row₀ j) (row₁ j) ≤ C) :
    LipschitzWith (Δ*(n+1)+C) (rowHomotopy row₀ row₁ n hsource htarget) := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨r,u⟩ ⟨s,v⟩
  let F := rowHomotopy row₀ row₁ n hsource htarget
  have hu : dist (F (r,u)) (F (r,v)) ≤ (Δ*(n+1) : ℝ≥0)*dist u v :=
    (rowHomotopy_path_time_lipschitz row₀ row₁ n hsource htarget Δ hedges₀ hedges₁ r).dist_le_mul u v
  have hs : dist (F (r,v)) (F (s,v)) ≤ C*dist r s :=
    interpolated_row_parameter_bound row₀ row₁ n C hvertices r s v
  calc
    _ ≤ dist (F (r,u)) (F (r,v)) + dist (F (r,v)) (F (s,v)) := dist_triangle _ _ _
    _ ≤ (Δ*(n+1) : ℝ≥0)*dist u v + C*dist r s := add_le_add hu hs
    _ ≤ (Δ*(n+1) : ℝ≥0)*dist (r,u) (s,v) + C*dist (r,u) (s,v) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      · exact mul_le_mul_of_nonneg_left (le_max_left _ _) C.property
    _ = (Δ*(n+1)+C : ℝ≥0)*dist (r,u) (s,v) := by simp [add_mul]

/-- A row whose endpoints are named independently of its vertex list. -/
structure BasedRow (n : ℕ) (p q : E) where
  vertices : ℕ → E
  source : vertices 0 = p
  target : vertices (n+1) = q

namespace BasedRow

variable {n : ℕ} {p q : E}

def path (R : BasedRow n p q) : Path p q :=
  (asPath R.vertices n).cast R.source.symm R.target.symm

def homotopy (R S : BasedRow n p q) : R.path.Homotopy S.path :=
  ((rowHomotopy R.vertices S.vertices n (R.source.trans S.source.symm)
    (R.target.trans S.target.symm)).pathCast R.source.symm R.target.symm).cast rfl (by
      apply Path.ext
      rfl)

theorem homotopy_path_time_lipschitz (R S : BasedRow n p q) (Δ : ℝ≥0)
    (hR : ∀ j ≤ n, dist (R.vertices j) (R.vertices (j+1)) ≤ Δ)
    (hS : ∀ j ≤ n, dist (S.vertices j) (S.vertices (j+1)) ≤ Δ) (r : unitInterval) :
    LipschitzWith (Δ*(n+1)) ((R.homotopy S).eval r) :=
  rowHomotopy_path_time_lipschitz R.vertices S.vertices n
    (R.source.trans S.source.symm) (R.target.trans S.target.symm) Δ hR hS r



end BasedRow





theorem exists_slot (T : ℕ) (_hT : 0 < T) (n : ℕ) (u : ℝ)
    (hu₀ : 0 ≤ u) (hu₁ : u ≤ ((n : ℝ)+1)/T) :
    ∃ j ≤ n, (j : ℝ)/T ≤ u ∧ u ≤ ((j : ℝ)+1)/T := by
  induction n with
  | zero => exact ⟨0,le_rfl,by simpa using hu₀,hu₁⟩
  | succ n ih =>
    by_cases hc : u ≤ ((n : ℝ)+1)/T
    · obtain ⟨j,hj,h₀,h₁⟩ := ih hc
      exact ⟨j,hj.trans (Nat.le_succ n),h₀,h₁⟩
    · exact ⟨n+1,le_rfl,by simpa using (le_of_lt (lt_of_not_ge hc)),hu₁⟩

/-- All slots stay inside the union of their prescribed convex charts. -/
theorem rowHomotopy_mem_charts (row₀ row₁ : ℕ → E) (n : ℕ)
    (hsource : row₀ 0 = row₁ 0) (htarget : row₀ (n+1) = row₁ (n+1))
    {S : Set E} (hcharts : ∀ j ≤ n, ∃ F : Set E,
      Convex ℝ F ∧ F ⊆ S ∧ row₀ j ∈ F ∧ row₀ (j+1) ∈ F ∧
        row₁ j ∈ F ∧ row₁ (j+1) ∈ F) (z : unitInterval × unitInterval) :
    rowHomotopy row₀ row₁ n hsource htarget z ∈ S := by
  have hne : (n : ℝ)+1 ≠ 0 := by positivity
  have hupper : (z.2 : ℝ) ≤ ((n : ℝ)+1)/((n+1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one, hne] using z.2.property.2
  obtain ⟨j,hj,h₀,h₁⟩ := exists_slot (n+1) (Nat.succ_pos n) n (z.2 : ℝ) z.2.property.1 hupper
  obtain ⟨F,hconv,hsub,ha,hb,hc,hd⟩ := hcharts j hj
  exact hsub (interpolated_row_mem_on_slot (n+1) (Nat.succ_pos n) row₀ row₁ n j hj z.1
    hconv ha hb hc hd (z.2 : ℝ) h₀ h₁)











end

end AbelianTargets.FixedSlots


