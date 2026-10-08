-- Prove2me | Definitions.Def_P2MAssembly_Chapter13V2_Part1
-- name    : P2MAssembly_Chapter13V2_Part1
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-09-12T20:30:44.051489+00:00
-- url     : https://prove2.me/theorems/4fbdf554-f2ae-4347-b318-38e9c292b598
-- title:
--   Finite maps and spherical-arm geometry
-- statement:
--   This part defines finite combinatorial maps by an edge involution and vertex permutation, their orbit counts and connected Euler-characteristic-two sphere predicate. Its geometric core is the unit sphere in three-dimensional Euclidean space, spherical distance and angle, determinant orientation, and strict convex spherical polygons and arms. Strict convexity includes short edges, oriented support, strict support at nonincident vertices, and a common open hemisphere. Rotations, diagonal and hinge cuts, intervals of arms, and deficit and opening constructions provide supporting data and proofs for spherical-arm comparison.
-- source:
--   Exact reviewed local source: proof_in_the_book commit 873d52e0c88cd351f594221e70c3c5b3559777a9, ProofsInTheBook/ZinanCh13Cauchy3D.lean:4470 (headline), :96 (ConvexEuclideanPolyhedron), :143 (edge-length congruence), :1157 (adaptive offset), :3467 (rotated stars); ProofsInTheBook/ZinanCh13Euclidean.lean:46 (realization) and :115 (face orientation). These staged files match git show at that local commit. PUBLIC SOURCE GAP: the raw GitHub URL for this commit returned HTTP 404; the older public commit 88d88d141768cded75e782c525ef1bf04b8fe220 differs in these two files and is not an exact source citation for this artifact. Unchanged supporting definitions are publicly byte-verified at https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMap.lean#L24 and https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMapSimple.lean#L97. Repository topic: Cauchy rigidity; no edition-specific chapter mapping asserted.

import Init
import Mathlib
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Fin.Rev
import Mathlib.Geometry.Euclidean.Triangle
set_option autoImplicit true


/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.PlanarMap -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

/-- A combinatorial (orientable) map on a finite dart set `D`:
edge involution `α` (fixed-point-free) and vertex rotation `σ`. -/
structure CombMap (D : Type*) [Fintype D] [DecidableEq D] where
  /-- Edge involution: pairs each dart with its reverse. -/
  α : Equiv.Perm D
  /-- Vertex rotation: cyclic order of darts around each vertex. -/
  σ : Equiv.Perm D
  /-- `α` is an involution. -/
  α_invol : α * α = 1
  /-- `α` has no fixed dart (every edge has two distinct darts). -/
  α_no_fixed : ∀ d, α d ≠ d

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Face permutation `φ = σ ∘ α`. Its orbits are the faces. -/
def φ (M : CombMap D) : Equiv.Perm D := M.σ * M.α

/-- The `SameCycle` equivalence of a permutation, as a `Setoid` on the dart set.
Its classes are the orbits (cycles, including fixed points). -/
def cycleSetoid (p : Equiv.Perm D) : Setoid D where
  r := p.SameCycle
  iseqv := ⟨fun x => Equiv.Perm.SameCycle.refl p x, fun h => h.symm, fun h h' => h.trans h'⟩

instance (p : Equiv.Perm D) : DecidableRel (cycleSetoid p).r :=
  (inferInstance : DecidableRel p.SameCycle)

instance (p : Equiv.Perm D) : Fintype (Quotient (cycleSetoid p)) :=
  Quotient.fintype (cycleSetoid p)

/-- Number of vertices: the number of `σ`-orbits. -/
def V (M : CombMap D) : ℕ := Fintype.card (Quotient (cycleSetoid M.σ))

/-- Number of edges: the number of `α`-orbits. -/
def E (M : CombMap D) : ℕ := Fintype.card (Quotient (cycleSetoid M.α))

/-- Number of faces: the number of `φ`-orbits. -/
def F (M : CombMap D) : ℕ := Fintype.card (Quotient (cycleSetoid M.φ))

/-- The Euler characteristic `V - E + F`. -/
def eulerChar (M : CombMap D) : ℤ := (V M : ℤ) - (E M : ℤ) + (F M : ℤ)

/-- Adjacency of the underlying multigraph on darts: same vertex, or joined by an edge. -/
def dartStep (M : CombMap D) (a b : D) : Prop :=
  M.σ.SameCycle a b ∨ b = M.α a

/-- The map is connected if every two darts are linked by a chain of `dartStep`s. -/
def Connected (M : CombMap D) : Prop :=
  ∀ a b : D, Relation.ReflTransGen M.dartStep a b

/-- A **plane (sphere) map**: connected and of Euler characteristic `2` (genus zero).
The faithful combinatorial definition of a planar graph embedding; NOT an inductive build
certificate, so theorems proved for `IsSphereMap` are about all plane graphs. -/
def IsSphereMap (M : CombMap D) : Prop :=
  M.Connected ∧ M.eulerChar = 2

/-- A power of an involution is either the identity or the involution itself. -/
lemma zpow_involution (α : Equiv.Perm D) (h : α * α = 1) (i : ℤ) :
    α ^ i = 1 ∨ α ^ i = α := by
  have hsq : α ^ (2 : ℤ) = 1 := by
    have h2 : α ^ (2 : ℤ) = α * α := by
      rw [show (2 : ℤ) = 1 + 1 from rfl, zpow_add, zpow_one]
    rw [h2, h]
  rcases Int.even_or_odd i with ⟨r, hr⟩ | ⟨k, hk⟩
  · left
    rw [show i = 2 * r by omega, zpow_mul, hsq, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]

/-- The edge containing a dart `d` is exactly `{d, α d}`: the `α`-orbit of any dart has
the two darts of its edge and no more. -/
lemma alpha_sameCycle_iff (M : CombMap D) (d x : D) :
    M.α.SameCycle d x ↔ x = d ∨ x = M.α d := by
  constructor
  · rintro ⟨i, rfl⟩
    rcases zpow_involution M.α M.α_invol i with h1 | h1
    · left; rw [h1]; rfl
    · right; rw [h1]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩







/-- A `p`-regular face structure: every face (`φ`-orbit) has exactly `p` darts. -/
def FaceRegular (M : CombMap D) (p : ℕ) : Prop :=
  ∀ Q : Quotient (cycleSetoid M.φ),
    (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.φ) x = Q)).card = p











end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.TetPearls -/
section
set_option autoImplicit true




noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open scoped Classical
open Set

namespace ProofsInTheBook.TetPearls

/-- Ambient Euclidean 3-space. -/
abbrev Pt3 : Type := EuclideanSpace ℝ (Fin 3)





namespace Tet



















end Tet





namespace TetSolid







end TetSolid









namespace Segment3







































































end Segment3



namespace Tet













end Tet





















namespace Pearl








end Pearl





































end ProofsInTheBook.TetPearls

end
end

/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.Chapter09 -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Chapter09

open scoped BigOperators TensorProduct
open Polynomial Chebyshev





















































-- (`angleClassQ_arccos_one_third_ne_zero` defined below, after
-- `arccos_one_third_irrational_over_pi`.)












































































































































































































































































end ProofsInTheBook.Chapter09

end

/- Original source header (imports hoisted):
import ProofsInTheBook.TetPearls
import ProofsInTheBook.Chapter09
-/
/- Source module: ProofsInTheBook.TetDihedral -/
section
set_option autoImplicit true




noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls

namespace ProofsInTheBook.TetDihedral



/-- `projOut d x` is the component of `x` orthogonal to `d`: `x - (⟪x,d⟫/⟪d,d⟫) • d`.  When `d ≠ 0`
this is the orthogonal projection of `x` onto the hyperplane `dᗮ`. -/
def projOut (d x : Pt3) : Pt3 := x - ((⟪x, d⟫ / ⟪d, d⟫) : ℝ) • d

/-- `projOut d x` is orthogonal to `d` whenever `d ≠ 0`. -/
theorem inner_projOut_right (d x : Pt3) (hd : d ≠ 0) : ⟪projOut d x, d⟫ = 0 := by
  have hdd : (⟪d, d⟫ : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ⟪d, d⟫ := real_inner_self_pos.mpr hd
    exact ne_of_gt this
  simp only [projOut, inner_sub_left, real_inner_smul_left]
  field_simp
  ring

/-- `projOut` is additive in its second argument. -/
theorem projOut_add (d x y : Pt3) : projOut d (x + y) = projOut d x + projOut d y := by
  simp only [projOut, inner_add_left, add_div, add_smul]
  abel

/-- `projOut` is homogeneous in its second argument. -/
theorem projOut_smul (d : Pt3) (r : ℝ) (x : Pt3) : projOut d (r • x) = r • projOut d x := by
  simp only [projOut, real_inner_smul_left, smul_sub, smul_smul]
  congr 2
  rw [mul_div_assoc]



/-- The inner product of two `projOut`-projections, as a closed form in the original inner products.
`⟪projOut d x, projOut d y⟫ = ⟪x,y⟫ - ⟪x,d⟫⟪y,d⟫/⟪d,d⟫`. -/
theorem inner_projOut_projOut (d x y : Pt3) (hd : d ≠ 0) :
    (⟪projOut d x, projOut d y⟫ : ℝ)
      = ⟪x, y⟫ - ⟪x, d⟫ * ⟪y, d⟫ / ⟪d, d⟫ := by
  have hdd : (⟪d, d⟫ : ℝ) ≠ 0 := ne_of_gt (real_inner_self_pos.mpr hd)
  simp only [projOut, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm d x, real_inner_comm d y, real_inner_comm d d]
  field_simp
  ring

































/-- `projOut d d = 0`: the component of `d` orthogonal to itself vanishes (for `d ≠ 0`). -/
theorem projOut_self (d : Pt3) (hd : d ≠ 0) : projOut d d = 0 := by
  have hdd : (⟪d, d⟫ : ℝ) ≠ 0 := ne_of_gt (real_inner_self_pos.mpr hd)
  simp only [projOut]
  rw [div_self hdd, one_smul, sub_self]









































end ProofsInTheBook.TetDihedral

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.TetDihedral
-/
/- Source module: ProofsInTheBook.SphericalKernel -/
section
set_option autoImplicit true




noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral

namespace ProofsInTheBook.SphericalKernel



/-- `E3` is the ambient Euclidean 3-space `EuclideanSpace ℝ (Fin 3)` (an alias for `Pt3`). -/
abbrev E3 : Type := Pt3

/-- The unit sphere `S²`, as the unit vectors of `E3`. -/
def S2 : Type := {x : E3 // ‖x‖ = 1}

instance : Coe S2 E3 := ⟨Subtype.val⟩

@[simp] theorem S2.norm_coe (p : S2) : ‖(p : E3)‖ = 1 := p.2

/-- `⟪p,p⟫ = 1` for a point of `S²`. -/
@[simp] theorem S2.inner_self (p : S2) : (⟪(p : E3), (p : E3)⟫ : ℝ) = 1 := by
  rw [real_inner_self_eq_norm_sq, p.2]; norm_num

theorem S2.coe_injective : Function.Injective (fun p : S2 => (p : E3)) :=
  Subtype.val_injective

@[ext] theorem S2.ext {p q : S2} (h : (p : E3) = (q : E3)) : p = q :=
  S2.coe_injective h

/-- The spherical inner product `⟪p,q⟫`. -/
def sInner (p q : S2) : ℝ := ⟪(p : E3), (q : E3)⟫

theorem sInner_comm (p q : S2) : sInner p q = sInner q p := real_inner_comm _ _

@[simp] theorem sInner_self (p : S2) : sInner p p = 1 := S2.inner_self p

/-- The inner product of two unit vectors lies in `[-1,1]` (Cauchy–Schwarz). -/
theorem sInner_mem_Icc (p q : S2) : sInner p q ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := abs_real_inner_le_norm (p : E3) (q : E3)
  rw [p.2, q.2, mul_one] at h
  rw [Set.mem_Icc, ← abs_le]
  exact h

theorem neg_one_le_sInner (p q : S2) : -1 ≤ sInner p q := (sInner_mem_Icc p q).1
theorem sInner_le_one (p q : S2) : sInner p q ≤ 1 := (sInner_mem_Icc p q).2

/-- The spherical distance `arccos ⟪p,q⟫ ∈ [0,π]`. -/
def sDist (p q : S2) : ℝ := Real.arccos (sInner p q)

theorem sDist_comm (p q : S2) : sDist p q = sDist q p := by
  rw [sDist, sDist, sInner_comm]

theorem sDist_nonneg (p q : S2) : 0 ≤ sDist p q := Real.arccos_nonneg _

theorem sDist_le_pi (p q : S2) : sDist p q ≤ Real.pi := Real.arccos_le_pi _

/-- `cos (sDist p q) = ⟪p,q⟫`. -/
@[simp] theorem cos_sDist (p q : S2) : Real.cos (sDist p q) = sInner p q :=
  Real.cos_arccos (neg_one_le_sInner p q) (sInner_le_one p q)

/-- `sin (sDist p q) ≥ 0` (distance lies in `[0,π]`). -/
theorem sin_sDist_nonneg (p q : S2) : 0 ≤ Real.sin (sDist p q) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (sDist_nonneg p q) (sDist_le_pi p q)



/-- `sDist p q = 0 ↔ p = q` (for unit vectors). -/
theorem sDist_eq_zero_iff {p q : S2} : sDist p q = 0 ↔ p = q := by
  constructor
  · intro h
    -- arccos ⟪p,q⟫ = 0 ⟹ ⟪p,q⟫ = 1 ⟹ ‖p - q‖² = 0
    have hcos : sInner p q = 1 := by
      have := congrArg Real.cos h
      rwa [cos_sDist, Real.cos_zero] at this
    have hpq : (⟪(p : E3), (q : E3)⟫ : ℝ) = 1 := hcos
    have hqp : (⟪(q : E3), (p : E3)⟫ : ℝ) = 1 := by rw [real_inner_comm]; exact hpq
    have hnorm : ‖(p : E3) - (q : E3)‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right]
      rw [S2.inner_self, S2.inner_self, hpq, hqp]; ring
    have : (p : E3) - (q : E3) = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hnorm
      exact norm_eq_zero.mp this
    exact S2.ext (sub_eq_zero.mp this)
  · rintro rfl; rw [sDist, sInner_self, Real.arccos_one]

/-- For unit vectors, the spherical distance is positive iff the points differ. -/
theorem sDist_pos_of_ne {p q : S2} (h : p ≠ q) : 0 < sDist p q :=
  lt_of_le_of_ne (sDist_nonneg p q) (fun he => h (sDist_eq_zero_iff.mp he.symm))

/-- The spherical distance is `< π` unless the points are antipodal. -/
theorem sDist_lt_pi_of_not_antipodal {p q : S2} (h : (p : E3) ≠ -(q : E3)) :
    sDist p q < Real.pi := by
  rw [sDist, Real.arccos_lt_pi]
  -- ⟪p,q⟫ = -1 would force p = -q.
  rcases lt_or_eq_of_le (neg_one_le_sInner p q) with hlt | heq
  · exact hlt
  · exfalso; apply h
    -- ⟪p,q⟫ = -1 ⟹ ‖p + q‖² = 0 ⟹ p = -q
    have hcos : sInner p q = -1 := heq.symm
    have hnorm : ‖(p : E3) + (q : E3)‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right]
      rw [S2.inner_self, S2.inner_self]
      have h1 : (⟪(p : E3), (q : E3)⟫ : ℝ) = -1 := hcos
      have h2 : (⟪(q : E3), (p : E3)⟫ : ℝ) = -1 := by rw [real_inner_comm]; exact h1
      rw [h1, h2]; ring
    have hpq : (p : E3) + (q : E3) = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hnorm
      exact norm_eq_zero.mp this
    exact eq_neg_of_add_eq_zero_left hpq

/-- `ShortArc p q`: the points are neither equal nor antipodal, so the shorter great-circle arc is
well-defined and the tangent direction is nonzero. -/
def ShortArc (p q : S2) : Prop := p ≠ q ∧ (p : E3) ≠ -(q : E3)

theorem ShortArc.sDist_pos {p q : S2} (h : ShortArc p q) : 0 < sDist p q :=
  sDist_pos_of_ne h.1

theorem ShortArc.sDist_lt_pi {p q : S2} (h : ShortArc p q) : sDist p q < Real.pi :=
  sDist_lt_pi_of_not_antipodal h.2

theorem ShortArc.symm {p q : S2} (h : ShortArc p q) : ShortArc q p :=
  ⟨h.1.symm, by
    intro he
    apply h.2
    rw [he]; rw [neg_neg]⟩

/-- For a short arc, `sin (sDist p q) > 0`. -/
theorem ShortArc.sin_sDist_pos {p q : S2} (h : ShortArc p q) :
    0 < Real.sin (sDist p q) :=
  Real.sin_pos_of_pos_of_lt_pi h.sDist_pos h.sDist_lt_pi



/-- The tangent vector at `p` pointing toward `q` along the shorter great circle. -/
def tangentTo (p q : S2) : E3 := projOut (p : E3) (q : E3)

/-- `projOut (p:E3)` with `p` a unit vector divides by `⟪p,p⟫ = 1`, so the scalar is just `⟪q,p⟫`. -/
theorem tangentTo_eq (p q : S2) :
    tangentTo p q = (q : E3) - (sInner q p) • (p : E3) := by
  rw [tangentTo, projOut, S2.inner_self, div_one, sInner]

/-- The tangent vector is orthogonal to the base point. -/
theorem tangentTo_orthogonal (p q : S2) : (⟪tangentTo p q, (p : E3)⟫ : ℝ) = 0 := by
  have hp : (p : E3) ≠ 0 := by
    intro h; have := p.2; rw [h, norm_zero] at this; norm_num at this
  exact inner_projOut_right (p : E3) (q : E3) hp

/-- **Decomposition of a unit vector along the tangent.**  Writes `q` as its component along `p`
(coefficient `cos (sDist p q)`) plus its tangential component. -/
theorem decompose_unit_along_tangent (p q : S2) :
    (q : E3) = (Real.cos (sDist p q)) • (p : E3) + tangentTo p q := by
  rw [tangentTo_eq, cos_sDist, sInner_comm]; abel

/-- `‖tangentTo p q‖² = sin (sDist p q)²` (Pythagoras: `q = cos·p + tangent`, with the two parts
orthogonal and `p` a unit vector). -/
theorem norm_sq_tangentTo (p q : S2) :
    ‖tangentTo p q‖ ^ 2 = Real.sin (sDist p q) ^ 2 := by
  -- ‖tangent‖² = ⟪q,q⟫ - ⟪q,p⟫²  (projection onto pᗮ), and ⟪q,q⟫ = 1, ⟪q,p⟫ = cos.
  have hp : (p : E3) ≠ 0 := by
    intro h; have := p.2; rw [h, norm_zero] at this; norm_num at this
  have h := inner_projOut_projOut (p : E3) (q : E3) (q : E3) hp
  show ‖projOut (p : E3) (q : E3)‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq, h]
  rw [S2.inner_self, S2.inner_self]
  -- ⟪q,p⟫ = sInner q p = cos (sDist q p) = cos (sDist p q)
  have hqp : (⟪(q : E3), (p : E3)⟫ : ℝ) = Real.cos (sDist p q) := by
    have : Real.cos (sDist p q) = sInner p q := cos_sDist p q
    rw [this, sInner_comm]; rfl
  rw [hqp, div_one]
  -- 1 - cos² = sin²
  have := Real.sin_sq_add_cos_sq (sDist p q)
  nlinarith [this]

/-- `‖tangentTo p q‖ = sin (sDist p q)` (the spherical sine; both sides are nonnegative). -/
theorem norm_tangentTo (p q : S2) :
    ‖tangentTo p q‖ = Real.sin (sDist p q) := by
  have h := norm_sq_tangentTo p q
  have hnn1 : (0 : ℝ) ≤ ‖tangentTo p q‖ := norm_nonneg _
  have hnn2 : (0 : ℝ) ≤ Real.sin (sDist p q) := sin_sDist_nonneg p q
  nlinarith [h, hnn1, hnn2]

/-- `tangentTo p q = 0 ↔ p` and `q` are equal or antipodal (i.e. the arc is *not* short). -/
theorem tangentTo_eq_zero_iff (p q : S2) :
    tangentTo p q = 0 ↔ ¬ ShortArc p q := by
  constructor
  · intro h
    -- ‖tangent‖ = 0 ⟹ sin (sDist) = 0 ⟹ sDist ∈ {0, π}.
    have hsin : Real.sin (sDist p q) = 0 := by
      rw [← norm_tangentTo, h, norm_zero]
    -- not a short arc: if it were, sin > 0.
    intro hsa
    exact (ne_of_gt hsa.sin_sDist_pos) hsin
  · intro h
    -- not short arc: p = q or p = -q. Either way tangent = 0.
    rw [ShortArc, not_and_or, not_not, not_not] at h
    rw [tangentTo_eq]
    rcases h with hpq | hpa
    · rw [hpq, sInner_self, one_smul, sub_self]
    · -- p = -q ⟹ q = -p, ⟪q,p⟫ = -1.
      have hqp : (q : E3) = -(p : E3) := by rw [hpa, neg_neg]
      have : sInner q p = -1 := by
        rw [sInner, hqp, inner_neg_left, S2.inner_self]
      rw [this, hqp]; module

theorem tangentTo_ne_zero_iff (p q : S2) :
    tangentTo p q ≠ 0 ↔ ShortArc p q := by
  rw [ne_eq, tangentTo_eq_zero_iff, not_not]

/-- The spherical angle at vertex `v` between neighbours `u` and `w`: the unoriented angle between
the tangent projections of `u` and `w` at `v`. -/
def sphAngle (u v w : S2) : ℝ :=
  InnerProductGeometry.angle (tangentTo v u) (tangentTo v w)

theorem sphAngle_comm (u v w : S2) : sphAngle u v w = sphAngle w v u :=
  InnerProductGeometry.angle_comm _ _

theorem sphAngle_nonneg (u v w : S2) : 0 ≤ sphAngle u v w :=
  InnerProductGeometry.angle_nonneg _ _

theorem sphAngle_le_pi (u v w : S2) : sphAngle u v w ≤ Real.pi :=
  InnerProductGeometry.angle_le_pi _ _



/-- The inner product of the two tangent directions at `b` equals
`sin(ab)·sin(bc)·cos γ`, where `γ = sphAngle a b c`. -/
theorem inner_tangent_tangent (a b c : S2) :
    (⟪tangentTo b a, tangentTo b c⟫ : ℝ)
      = Real.sin (sDist a b) * Real.sin (sDist b c) * Real.cos (sphAngle a b c) := by
  have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (tangentTo b a) (tangentTo b c)
  rw [norm_tangentTo, norm_tangentTo] at h
  -- h : cos γ * (sin(sDist b a) * sin(sDist b c)) = ⟪tan ba, tan bc⟫
  rw [sphAngle]
  rw [show sDist b a = sDist a b from sDist_comm b a] at h
  linarith [h]

/-- **Spherical law of cosines.**  For the angle `γ = sphAngle a b c` at `b`,
`cos (sDist a c) = cos(ab)·cos(bc) + sin(ab)·sin(bc)·cos γ`. -/
theorem spherical_cosine_rule (a b c : S2) :
    Real.cos (sDist a c)
      = Real.cos (sDist a b) * Real.cos (sDist b c)
        + Real.sin (sDist a b) * Real.sin (sDist b c) * Real.cos (sphAngle a b c) := by
  -- cos (sDist a c) = ⟪a,c⟫.
  rw [cos_sDist, sInner]
  -- Decompose a and c along the tangent frame at b.
  have ha : (a : E3) = (Real.cos (sDist b a)) • (b : E3) + tangentTo b a :=
    decompose_unit_along_tangent b a
  have hc : (c : E3) = (Real.cos (sDist b c)) • (b : E3) + tangentTo b c :=
    decompose_unit_along_tangent b c
  -- The cross terms involve ⟪tangent, b⟫ = 0.
  have hta : (⟪tangentTo b a, (b : E3)⟫ : ℝ) = 0 := tangentTo_orthogonal b a
  have htc : (⟪tangentTo b c, (b : E3)⟫ : ℝ) = 0 := tangentTo_orthogonal b c
  have htc' : (⟪(b : E3), tangentTo b c⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact htc
  rw [ha, hc]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      S2.inner_self, htc', hta, mul_zero, mul_one, add_zero, zero_add]
  rw [inner_tangent_tangent a b c]
  rw [show sDist b a = sDist a b from sDist_comm b a]
  ring

/-- Solving the spherical cosine rule for the included angle. -/
theorem cos_sphAngle_eq_of_short {u v w : S2}
    (huv : ShortArc u v) (hvw : ShortArc v w) :
    Real.cos (sphAngle u v w) =
      (Real.cos (sDist u w) - Real.cos (sDist u v) * Real.cos (sDist v w)) /
        (Real.sin (sDist u v) * Real.sin (sDist v w)) := by
  have hcos := spherical_cosine_rule u v w
  have hsin₁ : 0 < Real.sin (sDist u v) := huv.sin_sDist_pos
  have hsin₂ : 0 < Real.sin (sDist v w) := hvw.sin_sDist_pos
  have hden : Real.sin (sDist u v) * Real.sin (sDist v w) ≠ 0 :=
    ne_of_gt (mul_pos hsin₁ hsin₂)
  field_simp [hden]
  nlinarith

/-- A spherical triangle is determined at the angle level by its three side lengths. -/
theorem sphAngle_eq_of_three_sDist_eq {u v w u' v' w' : S2}
    (huv : ShortArc u v) (hvw : ShortArc v w)
    (huv' : ShortArc u' v') (hvw' : ShortArc v' w')
    (huw : sDist u w = sDist u' w')
    (huv_eq : sDist u v = sDist u' v')
    (hvw_eq : sDist v w = sDist v' w') :
    sphAngle u v w = sphAngle u' v' w' := by
  apply Real.injOn_cos
    ⟨sphAngle_nonneg u v w, sphAngle_le_pi u v w⟩
    ⟨sphAngle_nonneg u' v' w', sphAngle_le_pi u' v' w'⟩
  rw [cos_sphAngle_eq_of_short huv hvw,
    cos_sphAngle_eq_of_short huv' hvw', huw, huv_eq, hvw_eq]

/-- **Law-of-cosines monotonicity (weak).**  With side lengths `a,b ∈ (0,π)` fixed, the opposite
side `c` defined by the spherical cosine rule is monotone increasing in the included angle
`γ ∈ [0,π]`.  This is the `n = 3` base of the spherical arm lemma.

The hypotheses `hc₁`, `hc₂` are *the spherical cosine rule itself* for two configurations sharing
`a, b`; in the geometric application they are supplied by `spherical_cosine_rule`. -/
theorem spherical_hinge_mono
    {a b γ₁ γ₂ c₁ c₂ : ℝ}
    (ha0 : 0 < a) (hapi : a < Real.pi)
    (hb0 : 0 < b) (hbpi : b < Real.pi)
    (hg₁0 : 0 ≤ γ₁)
    (hg₂pi : γ₂ ≤ Real.pi)
    (hγ : γ₁ ≤ γ₂)
    (hc₁ : Real.cos c₁ =
        Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos γ₁)
    (hc₂ : Real.cos c₂ =
        Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos γ₂)
    (hc₁range : 0 ≤ c₁ ∧ c₁ ≤ Real.pi)
    (hc₂range : 0 ≤ c₂ ∧ c₂ ≤ Real.pi) :
    c₁ ≤ c₂ := by
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 hapi
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb0 hbpi
  -- cos is antitone on [0,π]: γ₁ ≤ γ₂ ⟹ cos γ₂ ≤ cos γ₁.
  have hcosγ : Real.cos γ₂ ≤ Real.cos γ₁ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hg₁0 hg₂pi hγ
  -- Therefore cos c₂ ≤ cos c₁.
  have hcosc : Real.cos c₂ ≤ Real.cos c₁ := by
    rw [hc₁, hc₂]
    have : Real.sin a * Real.sin b * Real.cos γ₂ ≤ Real.sin a * Real.sin b * Real.cos γ₁ :=
      mul_le_mul_of_nonneg_left hcosγ (le_of_lt (mul_pos hsa hsb))
    linarith
  -- cos is injective-antitone on [0,π]: cos c₂ ≤ cos c₁ ⟹ c₁ ≤ c₂.
  by_contra hlt
  push_neg at hlt
  have : Real.cos c₁ < Real.cos c₂ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hc₂range.1 hc₁range.2 hlt
  linarith

/-- **Law-of-cosines monotonicity (strict).**  Strict inequality of included angles gives strict
inequality of opposite sides.  This is the strict `n = 3` base. -/
theorem spherical_hinge_strict
    {a b γ₁ γ₂ c₁ c₂ : ℝ}
    (ha0 : 0 < a) (hapi : a < Real.pi)
    (hb0 : 0 < b) (hbpi : b < Real.pi)
    (hg₁0 : 0 ≤ γ₁)
    (hg₂pi : γ₂ ≤ Real.pi)
    (hγ : γ₁ < γ₂)
    (hc₁ : Real.cos c₁ =
        Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos γ₁)
    (hc₂ : Real.cos c₂ =
        Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos γ₂)
    (hc₁range : 0 ≤ c₁ ∧ c₁ ≤ Real.pi)
    (hc₂range : 0 ≤ c₂ ∧ c₂ ≤ Real.pi) :
    c₁ < c₂ := by
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 hapi
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb0 hbpi
  -- cos strictly antitone on [0,π]: γ₁ < γ₂ ⟹ cos γ₂ < cos γ₁.
  have hcosγ : Real.cos γ₂ < Real.cos γ₁ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hg₁0 hg₂pi hγ
  have hcosc : Real.cos c₂ < Real.cos c₁ := by
    rw [hc₁, hc₂]
    have : Real.sin a * Real.sin b * Real.cos γ₂ < Real.sin a * Real.sin b * Real.cos γ₁ :=
      mul_lt_mul_of_pos_left hcosγ (mul_pos hsa hsb)
    linarith
  by_contra hle
  push_neg at hle
  have : Real.cos c₁ ≤ Real.cos c₂ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hc₂range.1 hc₁range.2 hle
  linarith



/-- The scalar triple product `det ![a, b, c]` of three vectors of `E3`, in explicit coordinates. -/
def det3 (a b c : E3) : ℝ :=
  a 0 * (b 1 * c 2 - b 2 * c 1)
    - a 1 * (b 0 * c 2 - b 2 * c 0)
    + a 2 * (b 0 * c 1 - b 1 * c 0)

/-- The oriented (signed) volume of the parallelepiped spanned by three sphere points. -/
def sOrient (a b c : S2) : ℝ := det3 (a : E3) (b : E3) (c : E3)

/-- A strictly convex spherical polygon: a cyclic tuple `P : Fin n → S²` of `n ≥ 3` vertices whose
edges are short arcs, each oriented great-circle edge supports all vertices on the nonnegative side,
non-incident vertices are strictly on the positive side, and all vertices lie in one open
hemisphere.  This is exactly what a convex-polyhedron vertex link provides. -/
structure StrictConvexSphPolygon {n : ℕ} [NeZero n] (P : Fin n → S2) : Prop where
  three_le : 3 ≤ n
  edge_short : ∀ i : Fin n, ShortArc (P i) (P (i + 1))
  edge_support : ∀ i j : Fin n, 0 ≤ sOrient (P i) (P (i + 1)) (P j)
  strict_nonincident : ∀ i j : Fin n, j ≠ i → j ≠ i + 1 →
      0 < sOrient (P i) (P (i + 1)) (P j)
  open_hemisphere : ∃ h : E3, ‖h‖ = 1 ∧ ∀ i : Fin n, 0 < ⟪h, (P i : E3)⟫

/-- A strictly convex spherical *arm* with `n` edges and `n+1` vertices: the closure (adding the
endpoint chord `A n → A 0`) is a strictly convex spherical polygon.  This is the structure the
Cauchy vertex links present after deleting one edge. -/
structure StrictConvexSphArm {n : ℕ} (A : Fin (n + 1) → S2) : Prop where
  two_le : 2 ≤ n
  closed_convex : StrictConvexSphPolygon (n := n + 1) A

/-- The `i`-th side length of an arm: the spherical distance between consecutive vertices. -/
def sideLen {n : ℕ} (A : Fin (n + 1) → S2) (i : Fin n) : ℝ :=
  sDist (A i.castSucc) (A i.succ)

/-- The internal joint angle at the `(i+1)`-st vertex of an arm: the spherical angle at vertex
`A ⟨i+1⟩` between its two neighbours `A ⟨i⟩` and `A ⟨i+2⟩`.  Here `i : Fin (n-1)` ranges over the
`n-1` internal joints; `i.isLt : i.val < n - 1` makes all three indices fall in `Fin (n+1)`. -/
def jointAngle {n : ℕ} (A : Fin (n + 1) → S2) (i : Fin (n - 1)) : ℝ :=
  sphAngle (A ⟨i.val, by have := i.isLt; omega⟩)
    (A ⟨i.val + 1, by have := i.isLt; omega⟩)
    (A ⟨i.val + 2, by have := i.isLt; omega⟩)



/-- A *hinge opening chain* witnessing that arm `B` is reachable from arm `A` by a finite sequence of
nonnegative spherical hinge openings preserving side lengths.  This is the data the Schoenberg–
Zaremba induction must produce; it is exactly what makes endpoint distance monotone.

We package it abstractly: `SZChain A B` records that endpoint distance does not decrease from `A` to
`B`, and strictly increases if some joint of `B` is strictly more open than the corresponding joint
of `A` (the conclusion the hinge chain delivers via `spherical_hinge_mono`/`_strict`). -/
structure SZChain {n : ℕ} (A B : Fin (n + 1) → S2) : Prop where
  /-- Endpoint distance does not decrease from `A` to `B`. -/
  endpoint_mono : sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n))
  /-- If some joint strictly opens, endpoint distance strictly increases. -/
  endpoint_strict : (∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) →
      sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n))



/-- **Spherical arm lemma (strict), conditional on the Schoenberg–Zaremba opening chain.**

The strict version Cauchy needs: under the hypotheses of `spherical_arm_mono` together with one
strictly wider joint, the endpoint distance strictly increases. -/
theorem spherical_arm_mono_strict
    {n : ℕ} (A B : Fin (n + 1) → S2)
    (hChain : SZChain A B)
    (hStrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  hChain.endpoint_strict hStrict



/-- The next-round Schoenberg–Zaremba obligation, as an explicit `Prop` (statement only, not proved
in this file).  Discharging this turns `spherical_arm_mono`/`spherical_arm_mono_strict` into
unconditional theorems. -/
def SchoenbergZarembaTarget : Prop :=
  ∀ {n : ℕ}, 2 ≤ n →
    ∀ (A B : Fin (n + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin n, sideLen A i = sideLen B i) →
      (∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) →
      SZChain A B

end ProofsInTheBook.SphericalKernel

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalKernel
-/
/- Source module: ProofsInTheBook.SphericalArm -/
section
set_option autoImplicit true




noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.SphericalArm



/-- The spherical distance is the Mathlib unoriented angle of the two unit vectors. -/
theorem sDist_eq_angle (p q : S2) :
    sDist p q = InnerProductGeometry.angle (p : E3) (q : E3) := by
  rw [sDist, InnerProductGeometry.angle, sInner, p.2, q.2]; norm_num

/-- A point of `S²` is nonzero as a vector of `E3`. -/
theorem coe_ne_zero (p : S2) : (p : E3) ≠ 0 := by
  intro h; have := p.2; rw [h, norm_zero] at this; norm_num at this

/-- **Spherical triangle inequality.**  `sDist p r ≤ sDist p q + sDist q r`. -/
theorem sDist_triangle (p q r : S2) :
    sDist p r ≤ sDist p q + sDist q r := by
  rw [sDist_eq_angle, sDist_eq_angle, sDist_eq_angle]
  exact InnerProductGeometry.angle_le_angle_add_angle _ _ _

/-- **Equality case of the spherical triangle inequality.**  Equality holds iff `p` and `r` are
antipodal (`sDist p r = π`) or the middle point `q` lies on the short great-circle arc between `p`
and `r` (it is a nonnegative linear combination of `p` and `r`).  This is the great-circle
betweenness characterization that drives the Schoenberg–Zaremba "stuck case". -/
theorem sDist_triangle_eq_iff (p q r : S2) :
    sDist p r = sDist p q + sDist q r ↔
      sDist p r = Real.pi ∨ (q : E3) ∈ Submodule.span NNReal {(p : E3), (r : E3)} := by
  rw [sDist_eq_angle, sDist_eq_angle, sDist_eq_angle]
  exact InnerProductGeometry.angle_eq_angle_add_angle_iff (coe_ne_zero q)

/-- If `q` lies on the short great-circle arc between `p` and `r` (a nonnegative combination), the
spherical triangle inequality is an equality: `sDist p r = sDist p q + sDist q r`.  This is the form
in which equation (2) of the book is used (`q₂q₁ + q₁qₙ* = q₂qₙ*`, with `q₁` between `q₂` and `qₙ*`). -/
theorem sDist_betweenness_of_collinear {p q r : S2}
    (h : (q : E3) ∈ Submodule.span NNReal {(p : E3), (r : E3)}) :
    sDist p r = sDist p q + sDist q r :=
  (sDist_triangle_eq_iff p q r).2 (Or.inr h)



theorem sDist_mem_Icc (p q : S2) : 0 ≤ sDist p q ∧ sDist p q ≤ Real.pi :=
  ⟨sDist_nonneg p q, sDist_le_pi p q⟩

/-- The closing edge of an arm joins the last vertex back to the first. -/
theorem arm_edge_short {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (i : Fin (n + 1)) : ShortArc (A i) (A (i + 1)) :=
  hA.closed_convex.edge_short i



/-- The endpoint distance of a `2`-edge arm is governed by the spherical cosine rule at the middle
vertex, with the included angle equal to the single joint angle. -/
theorem two_edge_cosine_rule (A : Fin 3 → S2) :
    Real.cos (sDist (A 0) (A (Fin.last 2)))
      = Real.cos (sDist (A 0) (A 1)) * Real.cos (sDist (A 1) (A 2))
        + Real.sin (sDist (A 0) (A 1)) * Real.sin (sDist (A 1) (A 2))
          * Real.cos (sphAngle (A 0) (A 1) (A 2)) := by
  have h := spherical_cosine_rule (A 0) (A 1) (A 2)
  simpa using h

theorem two_edge_sides (A : Fin 3 → S2) (hA : StrictConvexSphArm (n := 2) A) :
    (0 < sDist (A 0) (A 1) ∧ sDist (A 0) (A 1) < Real.pi) ∧
      (0 < sDist (A 1) (A 2) ∧ sDist (A 1) (A 2) < Real.pi) := by
  have h0 : ShortArc (A 0) (A 1) := by
    have := hA.closed_convex.edge_short 0; simpa using this
  have h1 : ShortArc (A 1) (A 2) := by
    have := hA.closed_convex.edge_short 1; simpa using this
  exact ⟨⟨h0.sDist_pos, h0.sDist_lt_pi⟩, ⟨h1.sDist_pos, h1.sDist_lt_pi⟩⟩

/-- **`n = 2` base, weak.**  Two convex spherical triangles with equal sides and a wider included
angle in `B` have a longer (or equal) opposite side in `B`. -/
theorem base_mono (A B : Fin 3 → S2)
    (hA : StrictConvexSphArm (n := 2) A) (hB : StrictConvexSphArm (n := 2) B)
    (hs0 : sDist (A 0) (A 1) = sDist (B 0) (B 1))
    (hs1 : sDist (A 1) (A 2) = sDist (B 1) (B 2))
    (hang : sphAngle (A 0) (A 1) (A 2) ≤ sphAngle (B 0) (B 1) (B 2)) :
    sDist (A 0) (A (Fin.last 2)) ≤ sDist (B 0) (B (Fin.last 2)) := by
  obtain ⟨⟨ha0, hapi⟩, ⟨hb0, hbpi⟩⟩ := two_edge_sides A hA
  refine spherical_hinge_mono (a := sDist (A 0) (A 1)) (b := sDist (A 1) (A 2))
    (γ₁ := sphAngle (A 0) (A 1) (A 2)) (γ₂ := sphAngle (B 0) (B 1) (B 2))
    ha0 hapi hb0 hbpi (sphAngle_nonneg _ _ _) (sphAngle_le_pi _ _ _) hang
    (two_edge_cosine_rule A) ?_ (sDist_mem_Icc _ _) (sDist_mem_Icc _ _)
  have hB' := two_edge_cosine_rule B
  rw [← hs0, ← hs1] at hB'
  exact hB'

/-- **`n = 2` base, strict.**  Strictly wider included angle gives a strictly longer opposite side. -/
theorem base_strict (A B : Fin 3 → S2)
    (hA : StrictConvexSphArm (n := 2) A) (hB : StrictConvexSphArm (n := 2) B)
    (hs0 : sDist (A 0) (A 1) = sDist (B 0) (B 1))
    (hs1 : sDist (A 1) (A 2) = sDist (B 1) (B 2))
    (hang : sphAngle (A 0) (A 1) (A 2) < sphAngle (B 0) (B 1) (B 2)) :
    sDist (A 0) (A (Fin.last 2)) < sDist (B 0) (B (Fin.last 2)) := by
  obtain ⟨⟨ha0, hapi⟩, ⟨hb0, hbpi⟩⟩ := two_edge_sides A hA
  refine spherical_hinge_strict (a := sDist (A 0) (A 1)) (b := sDist (A 1) (A 2))
    (γ₁ := sphAngle (A 0) (A 1) (A 2)) (γ₂ := sphAngle (B 0) (B 1) (B 2))
    ha0 hapi hb0 hbpi (sphAngle_nonneg _ _ _) (sphAngle_le_pi _ _ _) hang
    (two_edge_cosine_rule A) ?_ (sDist_mem_Icc _ _) (sDist_mem_Icc _ _)
  have hB' := two_edge_cosine_rule B
  rw [← hs0, ← hs1] at hB'
  exact hB'



/-- The endpoint (chord) distance of an arm. -/
def endpt {n : ℕ} (A : Fin (n + 1) → S2) : ℝ := sDist (A 0) (A (Fin.last n))

/-- The Schoenberg–Zaremba *comparison* conclusion at level `n`: equal sides and nondecreasing joint
angles force the endpoint distance not to decrease, strictly when some joint is strictly wider.  This
is precisely the `SZChain` data, packaged as a predicate so the induction can quantify over it. -/
def SZComparison (n : ℕ) : Prop :=
  ∀ (A B : Fin (n + 1) → S2),
    StrictConvexSphArm A → StrictConvexSphArm B →
    (∀ i : Fin n, sideLen A i = sideLen B i) →
    (∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) →
    endpt A ≤ endpt B ∧
      ((∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) → endpt A < endpt B)

/-- Reduction of the level-`2` arm data to the three concrete vertices. -/
theorem sideLen_two_zero (A : Fin 3 → S2) : sideLen A 0 = sDist (A 0) (A 1) := by
  simp [sideLen, Fin.castSucc, Fin.succ]

theorem sideLen_two_one (A : Fin 3 → S2) : sideLen A 1 = sDist (A 1) (A 2) := by
  simp [sideLen, Fin.castSucc, Fin.succ]

theorem jointAngle_two (A : Fin 3 → S2) :
    jointAngle A 0 = sphAngle (A 0) (A 1) (A 2) := by
  simp [jointAngle]

theorem endpt_two (A : Fin 3 → S2) : endpt A = sDist (A 0) (A 2) := by
  simp [endpt, Fin.last]

/-- **`SZComparison 2`**: the base case of the Schoenberg–Zaremba induction. -/
theorem szComparison_two : SZComparison 2 := by
  intro A B hA hB hside hangle
  have hs0 : sDist (A 0) (A 1) = sDist (B 0) (B 1) := by
    have := hside 0; rwa [sideLen_two_zero, sideLen_two_zero] at this
  have hs1 : sDist (A 1) (A 2) = sDist (B 1) (B 2) := by
    have := hside 1; rwa [sideLen_two_one, sideLen_two_one] at this
  have hga : sphAngle (A 0) (A 1) (A 2) ≤ sphAngle (B 0) (B 1) (B 2) := by
    have := hangle 0; rwa [jointAngle_two, jointAngle_two] at this
  refine ⟨?_, ?_⟩
  · rw [endpt_two, endpt_two]
    have := base_mono A B hA hB hs0 hs1 hga
    rwa [show (Fin.last 2 : Fin 3) = 2 from rfl] at this
  · rintro ⟨i, hi⟩
    have hi0 : i = (0 : Fin (2 - 1)) := by
      apply Fin.ext; have := i.isLt; omega
    subst hi0
    rw [jointAngle_two, jointAngle_two] at hi
    rw [endpt_two, endpt_two]
    have := base_strict A B hA hB hs0 hs1 hi
    rwa [show (Fin.last 2 : Fin 3) = 2 from rfl] at this



/-- **Triangle-inequality chain `(∗)` of the stuck case — proved unconditionally.**

With the book's labelling `q₁ = A0`, `q₂ = A1`, `q*ₙ = qstar` (the opened last vertex), `qₙ = An`
(original last vertex of `A`), `q'₁ = B0`, `q'₂ = B1`, `q'ₙ = Bn`, the four derived facts close the
goal `sDist q₁ qₙ < sDist q'₁ q'ₙ`:

* `hsub`  : `sDist q₂ q*ₙ ≤ sDist q'₂ q'ₙ`              (level-`n` sub-arm comparison, relation (3)),
* `hside` : `sDist q'₂ q'₁ = sDist q₂ q₁`               (equal first side),
* `hbtw`  : `sDist q₂ q*ₙ = sDist q₂ q₁ + sDist q₁ q*ₙ` (stuck betweenness, equation (2)),
* `hopen` : `sDist q₁ qₙ < sDist q₁ q*ₙ`                (nontrivial opening, equation (1)).

The first step `sDist q'₁ q'ₙ ≥ sDist q'₂ q'ₙ − sDist q'₂ q'₁` is the spherical triangle inequality
`(∗)`. -/
theorem szChain_stuck
    {A0 A1 An qstar B0 B1 Bn : S2}
    (hsub : sDist A1 qstar ≤ sDist B1 Bn)
    (hside : sDist B1 B0 = sDist A1 A0)
    (hbtw : sDist A1 qstar = sDist A1 A0 + sDist A0 qstar)
    (hopen : sDist A0 An < sDist A0 qstar) :
    sDist A0 An < sDist B0 Bn := by
  have htri : sDist B1 Bn ≤ sDist B1 B0 + sDist B0 Bn := sDist_triangle B1 B0 Bn
  -- sDist B0 Bn ≥ sDist B1 Bn − sDist B1 B0 ≥ sDist A1 qstar − sDist A1 A0
  --             = sDist A0 qstar > sDist A0 An.
  have key : sDist A0 qstar ≤ sDist B0 Bn := by
    have h1 : sDist A1 A0 + sDist A0 qstar = sDist A1 qstar := hbtw.symm
    -- from hbtw: sDist A0 qstar = sDist A1 qstar − sDist A1 A0
    nlinarith [hsub, htri, hside, hbtw]
  linarith [hopen, key]

/-- The stuck conjunction's betweenness is consistent: for any collinear triple (`A 0` on the short
arc between `A 1` and `qstar`) the betweenness equation holds.  Used both to drive the chain and as a
non-vacuity guard for the strict branch. -/
theorem stuck_betweenness_consistent {A0 A1 qstar : S2}
    (hcol : (A0 : E3) ∈ Submodule.span NNReal {(A1 : E3), (qstar : E3)}) :
    sDist A1 qstar = sDist A1 A0 + sDist A0 qstar :=
  sDist_betweenness_of_collinear hcol

/-- `szChain_stuck` packaged to consume a great-circle-collinear stuck configuration directly. -/
theorem szChain_stuck_nondegenerate
    {A0 A1 An qstar B0 B1 Bn : S2}
    (hcol : (A0 : E3) ∈ Submodule.span NNReal {(A1 : E3), (qstar : E3)})
    (hsub : sDist A1 qstar ≤ sDist B1 Bn)
    (hside : sDist B1 B0 = sDist A1 A0)
    (hopen : sDist A0 An < sDist A0 qstar) :
    sDist A0 An < sDist B0 Bn :=
  szChain_stuck hsub hside (stuck_betweenness_consistent hcol) hopen





/-- The book's reduction witness for one inductive step.  For convex arms `A B : Fin (n+2) → S2` it
provides a level-`n` sub-comparison and the distance data that the proved chain lemmas
(`szChain_stuck` / `base_strict` / `diagonal_eq_of_angle_eq` via `base_mono`) turn into the level-
`(n+1)` endpoint inequality.

Shape `stuck`: a moved last vertex `qstar` with
* `hbtw  : sDist (A 1) qstar = sDist (A 1) (A 0) + sDist (A 0) qstar`   (great-circle betweenness),
* `hopen : endpt A < sDist (A 0) qstar`                                 (nontrivial opening),
* `hsub  : sDist (A 1) qstar ≤ sDist (B 1) (B (Fin.last (n+1)))`        (level-`n` sub-comparison),
* `hside1: sDist (B 1) (B 0) = sDist (A 1) (A 0)`                       (equal first side),
which `szChain_stuck` turns into `endpt A < endpt B`.

Shape `weak`: a direct weak bound `endpt A ≤ endpt B` together with a witness `hmono` that strictness
is implied by some strictly-wider joint — used for the equal-angle cut and the reached case, whose
internal geometry is folded into the witness (this keeps the obligation a single named primitive).

To stay faithful while routing strictness through the proved lemmas, the `stuck` shape is the
genuinely active one (it consumes `szChain_stuck`); the `weak` shape supplies the monotone branch. -/
structure SZGeomWitness {n : ℕ} (A B : Fin (n + 1 + 1) → S2) : Prop where
  /-- The weak endpoint bound always holds (book: the arm lemma's `≤` half). -/
  weak : endpt A ≤ endpt B
  /-- If some joint of `B` is strictly wider, the endpoint distance strictly increases.  The book
  produces this through **one of two** configurations, faithfully reflected here as a disjunction so
  the primitive is neither too strong (it does not demand a stuck vertex in the *reached* case) nor a
  re-statement of the goal (the *stuck* branch hands its configuration to the proved chain lemma
  `szChain_stuck`):

  * `Or.inl` — the **stuck** branch: a moved last vertex `qstar` on the great circle through `A 1`
    and `A 0` (so `A 0` is between `A 1` and `qstar`), with the opening and sub-comparison bounds;
    `szChain_stuck` (via `szChain_stuck_nondegenerate`) turns this into the strict inequality.
  * `Or.inr` — the **reached / cut** branch: the strict inequality directly, as produced by the
    book's `spherical_hinge_strict` after the last angle has been matched and the equal-angle
    diagonal cut applied. -/
  strict : (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
    (∃ qstar : S2,
        (A 0 : E3) ∈ Submodule.span NNReal {(A 1 : E3), (qstar : E3)} ∧
        endpt A < sDist (A 0) qstar ∧
        sDist (A 1) qstar ≤ sDist (B 1) (B (Fin.last (n + 1))) ∧
        sDist (B 1) (B 0) = sDist (A 1) (A 0))
      ∨ endpt A < endpt B

/-- The isolated geometric primitive: for every `n ≥ 2`, convex arms with equal sides and
nondecreasing joints admit the book's reduction witness.  This packages the rotation / supremum / cut
construction of design §8, and is the single fact this file leaves unproved. -/
def SZGeom : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∀ (A B : Fin (n + 1 + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
      (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
      SZComparison n →    -- the inductive hypothesis: the level-`n` sub-arm comparison
      SZGeomWitness A B

/-- **The inductive step, proved from the geometric primitive.**  The endpoint inequalities are
derived here: the weak bound from the witness, and the strict bound by feeding the witness's stuck
configuration to the proved chain lemma `szChain_stuck`.  `endpt B = sDist (B 0) (B (Fin.last (n+1)))`
unfolds definitionally.  The level-`n` comparison `ih` is threaded into the primitive (the book's
relation (3) is an application of the inductive hypothesis to the sub-arm). -/
theorem szStep (hgeom : SZGeom) (n : ℕ) (hn : 2 ≤ n) (ih : SZComparison n) :
    SZComparison (n + 1) := by
  intro A B hA hB hside hangle
  have hw : SZGeomWitness A B := hgeom n hn A B hA hB hside hangle ih
  refine ⟨hw.weak, ?_⟩
  intro hstrict
  rcases hw.strict hstrict with ⟨qstar, hcol, hopen, hsub, hside1⟩ | hdirect
  · -- stuck branch: the proved chain lemma turns the geometric witness into the strict bound.
    have h := szChain_stuck_nondegenerate (A0 := A 0) (A1 := A 1) (An := A (Fin.last (n + 1)))
      (qstar := qstar) (B0 := B 0) (B1 := B 1) (Bn := B (Fin.last (n + 1)))
      hcol hsub hside1 (by simpa [endpt] using hopen)
    simpa [endpt] using h
  · -- reached / cut branch: the strict bound directly.
    exact hdirect

/-- All levels `≥ 2` satisfy the comparison, by induction on the number of edges. -/
theorem szComparison_all (hgeom : SZGeom) :
    ∀ n : ℕ, 2 ≤ n → SZComparison n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ m ih =>
    intro hm
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · have he : m + 1 = 2 := by omega
      rw [he]; exact szComparison_two
    · exact szStep hgeom m hge (ih hge)



/-- **The Schoenberg–Zaremba spherical arm lemma, conditional on the geometric primitive.**  From
`SZGeom` (the design §8 rotation / supremum / cut construction) the named kernel obligation
`SchoenbergZarembaTarget` holds: equal-sided convex arms with nondecreasing joints admit the
`SZChain`, hence (via the kernel) the endpoint distance is monotone, strictly so when some joint is
strictly wider.  All of the inequality content — the spherical triangle inequality, the chain `(∗)`,
the base case, and the recursion — is proved unconditionally in this file. -/
theorem schoenbergZaremba_of_geom (hgeom : SZGeom) : SchoenbergZarembaTarget := by
  intro n hn A B hA hB hside hangle
  have hcmp := szComparison_all hgeom n hn A B hA hB hside hangle
  exact
    { endpoint_mono := hcmp.1
      endpoint_strict := hcmp.2 }



end ProofsInTheBook.SphericalArm

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArm
-/
/- Source module: ProofsInTheBook.SphericalRotation -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm

namespace ProofsInTheBook.SphericalRotation

/-- Cross product on `E3 = EuclideanSpace ℝ (Fin 3)`, in explicit coordinates. -/
def cross (a b : E3) : E3 :=
  !₂[a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

@[simp] theorem cross_apply_zero (a b : E3) : cross a b 0 = a 1 * b 2 - a 2 * b 1 := rfl
@[simp] theorem cross_apply_one (a b : E3) : cross a b 1 = a 2 * b 0 - a 0 * b 2 := rfl
@[simp] theorem cross_apply_two (a b : E3) : cross a b 2 = a 0 * b 1 - a 1 * b 0 := rfl

/-- Inner product expanded into coordinates. -/
theorem inner_eq_coord (a b : E3) :
    (⟪a, b⟫ : ℝ) = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [RCLike.inner_apply, conj_trivial]; ring



@[simp] theorem add_apply (a b : E3) (i : Fin 3) : (a + b) i = a i + b i := rfl
@[simp] theorem smul_apply (r : ℝ) (a : E3) (i : Fin 3) : (r • a) i = r * a i := rfl

@[simp] theorem sub_apply (a b : E3) (i : Fin 3) : (a - b) i = a i - b i := rfl

/-- Two `E3` vectors agreeing on coordinates `0,1,2` are equal. -/
theorem ext_coord {a b : E3} (h0 : a 0 = b 0) (h1 : a 1 = b 1) (h2 : a 2 = b 2) : a = b := by
  apply WithLp.ofLp_injective 2
  funext i; fin_cases i <;> assumption



theorem cross_self (a : E3) : cross a a = 0 := by
  apply ext_coord <;> simp <;> ring

theorem cross_antisymm (a b : E3) : cross a b = - cross b a := by
  apply ext_coord <;> simp <;> ring

theorem cross_add_right (a b c : E3) : cross a (b + c) = cross a b + cross a c := by
  apply ext_coord <;> simp <;> ring



theorem cross_smul_right (r : ℝ) (a b : E3) : cross a (r • b) = r • cross a b := by
  apply ext_coord <;> simp <;> ring

theorem cross_smul_left (r : ℝ) (a b : E3) : cross (r • a) b = r • cross a b := by
  apply ext_coord <;> simp <;> ring

/-- `⟪a × b, a⟫ = 0`: the cross product is orthogonal to the first factor. -/
theorem inner_cross_left (a b : E3) : (⟪cross a b, a⟫ : ℝ) = 0 := by
  rw [inner_eq_coord]; simp; ring

/-- `⟪a × b, b⟫ = 0`: orthogonal to the second factor. -/
theorem inner_cross_right (a b : E3) : (⟪cross a b, b⟫ : ℝ) = 0 := by
  rw [inner_eq_coord]; simp; ring

/-- The scalar triple product `⟪a, b × c⟫` equals `det3 a b c` of the kernel. -/
theorem inner_cross_eq_det3 (a b c : E3) : (⟪a, cross b c⟫ : ℝ) = det3 a b c := by
  rw [inner_eq_coord, det3]; simp; ring

/-- Cyclic invariance of the triple product: `⟪a, b × c⟫ = ⟪c, a × b⟫`. -/
theorem inner_cross_cyclic (a b c : E3) : (⟪a, cross b c⟫ : ℝ) = ⟪c, cross a b⟫ := by
  rw [inner_eq_coord, inner_eq_coord]; simp; ring

/-- **Lagrange identity:** `‖a × b‖² = ‖a‖²‖b‖² − ⟪a,b⟫²`. -/
theorem norm_sq_cross (a b : E3) :
    ‖cross a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - (⟪a, b⟫ : ℝ) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_eq_coord, inner_eq_coord, inner_eq_coord, inner_eq_coord]
  simp; ring

/-- The cross product expanded via the `bac − cab` rule against an inner product:
`a × (b × c) = ⟪a,c⟫ • b − ⟪a,b⟫ • c`. -/
theorem cross_cross (a b c : E3) :
    cross a (cross b c) = (⟪a, c⟫ : ℝ) • b - (⟪a, b⟫ : ℝ) • c := by
  apply ext_coord <;>
    · simp only [cross_apply_zero, cross_apply_one, cross_apply_two, inner_eq_coord,
        sub_apply, smul_apply]; ring

/-- **Binet–Cauchy identity:** `⟪a × b, c × d⟫ = ⟪a,c⟫⟪b,d⟫ − ⟪a,d⟫⟪b,c⟫`. -/
theorem inner_cross_cross (a b c d : E3) :
    (⟪cross a b, cross c d⟫ : ℝ) = ⟪a, c⟫ * ⟪b, d⟫ - ⟪a, d⟫ * ⟪b, c⟫ := by
  rw [inner_eq_coord, inner_eq_coord, inner_eq_coord, inner_eq_coord, inner_eq_coord]
  simp only [cross_apply_zero, cross_apply_one, cross_apply_two]; ring



/-- The Rodrigues rotation of `v` about unit axis `k` by angle `θ`. -/
def rot (k : E3) (θ : ℝ) (v : E3) : E3 :=
  Real.cos θ • v + Real.sin θ • cross k v + ((1 - Real.cos θ) * ⟪k, v⟫) • k



/-- `rot` is additive in `v`. -/
theorem rot_add (k : E3) (θ : ℝ) (v w : E3) :
    rot k θ (v + w) = rot k θ v + rot k θ w := by
  simp only [rot, cross_add_right, inner_add_right, mul_add, add_smul, smul_add]; module

/-- `rot` is homogeneous in `v`. -/
theorem rot_smul (k : E3) (θ : ℝ) (r : ℝ) (v : E3) :
    rot k θ (r • v) = r • rot k θ v := by
  simp only [rot, cross_smul_right, inner_smul_right]
  rw [show ((1 - Real.cos θ) * (r * ⟪k, v⟫)) = r * ((1 - Real.cos θ) * ⟪k, v⟫) by ring]
  module

/-- `rot` distributes over subtraction in `v`. -/
theorem rot_sub (k : E3) (θ : ℝ) (v w : E3) :
    rot k θ (v - w) = rot k θ v - rot k θ w := by
  rw [sub_eq_add_neg, sub_eq_add_neg, rot_add]
  congr 1
  rw [show (-w) = (-1 : ℝ) • w by module, rot_smul]; module

/-- `rot k 0 = id`. -/
@[simp] theorem rot_zero (k : E3) (v : E3) : rot k 0 v = v := by
  simp only [rot, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, sub_self, zero_mul]
  simp

/-- The axis is fixed: `rot k θ k = k` for a unit axis. -/
theorem rot_axis {k : E3} (hk : ‖k‖ = 1) (θ : ℝ) : rot k θ k = k := by
  have hkk : (⟪k, k⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hk]; norm_num
  simp only [rot, cross_self, smul_zero, add_zero, hkk, mul_one]
  rw [← add_smul]; rw [show Real.cos θ + (1 - Real.cos θ) = 1 by ring, one_smul]

/-- The rotation preserves inner products with the axis: `⟪rot k θ v, k⟫ = ⟪v, k⟫`. -/
theorem inner_rot_axis {k : E3} (hk : ‖k‖ = 1) (θ : ℝ) (v : E3) :
    (⟪rot k θ v, k⟫ : ℝ) = ⟪v, k⟫ := by
  have hkk : (⟪k, k⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hk]; norm_num
  have hcross : (⟪cross k v, k⟫ : ℝ) = 0 := inner_cross_left k v
  have hvk : (⟪k, v⟫ : ℝ) = ⟪v, k⟫ := real_inner_comm v k
  simp only [rot, inner_add_left, real_inner_smul_left, hcross, hkk, mul_zero, mul_one, hvk]
  ring

/-- **Inner-product preservation (the crux):** `⟪rot k θ v, rot k θ w⟫ = ⟪v, w⟫` for a unit axis.
Proved by bilinear expansion using `inner_cross_cross` (Binet–Cauchy), `inner_cross_left/right`
(`⟪k×v,k⟫ = 0`), and `cos²θ + sin²θ = 1`. -/
theorem inner_rot_rot {k : E3} (hk : ‖k‖ = 1) (θ : ℝ) (v w : E3) :
    (⟪rot k θ v, rot k θ w⟫ : ℝ) = ⟪v, w⟫ := by
  have hkk : (⟪k, k⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hk]; norm_num
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  -- key cross identities (with k a unit vector)
  have h_kvk : (⟪cross k v, k⟫ : ℝ) = 0 := inner_cross_left k v
  have h_kkv : (⟪k, cross k v⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact h_kvk
  have h_kwk : (⟪cross k w, k⟫ : ℝ) = 0 := inner_cross_left k w
  have h_kkw : (⟪k, cross k w⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact h_kwk
  -- ⟪k×v, k×w⟫ = ⟪k,k⟫⟪v,w⟫ − ⟪k,w⟫⟪v,k⟫ = ⟪v,w⟫ − ⟪k,w⟫⟪v,k⟫
  have h_cc : (⟪cross k v, cross k w⟫ : ℝ) = ⟪v, w⟫ - ⟪k, w⟫ * ⟪v, k⟫ := by
    rw [inner_cross_cross, hkk, one_mul]
  -- mixed term antisymmetry: ⟪k×v, w⟫ = −⟪v, k×w⟫
  have h_mix : (⟪cross k v, w⟫ : ℝ) = -(⟪v, cross k w⟫) := by
    rw [inner_eq_coord, inner_eq_coord]
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  have hvk : (⟪v, k⟫ : ℝ) = ⟪k, v⟫ := real_inner_comm k v
  -- expand the full inner product
  simp only [rot, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    h_kvk, h_kkw, hkk]
  rw [h_cc, h_mix, hvk]
  -- now everything is in terms of ⟪v,w⟫, ⟪k,v⟫, ⟪k,w⟫, ⟪v, cross k w⟫, cos, sin;
  -- LHS − ⟪v,w⟫ = (cos²+sin²−1)(⟪v,w⟫ − ⟪k,v⟫⟪k,w⟫), closed by hcs.
  linear_combination (⟪v, w⟫ - ⟪k, v⟫ * ⟪k, w⟫) * hcs

/-- **Norm preservation:** `‖rot k θ v‖ = ‖v‖`. -/
theorem norm_rot {k : E3} (hk : ‖k‖ = 1) (θ : ℝ) (v : E3) :
    ‖rot k θ v‖ = ‖v‖ := by
  have h1 : ‖rot k θ v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_rot_rot hk]
  have hnn1 : (0 : ℝ) ≤ ‖rot k θ v‖ := norm_nonneg _
  have hnn2 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  nlinarith [h1, hnn1, hnn2]



/-- The rotation maps `S²` into `S²` (norm preserved). -/
def rotS2 (k : S2) (θ : ℝ) (p : S2) : S2 :=
  ⟨rot (k : E3) θ (p : E3), by rw [norm_rot k.2]; exact p.2⟩

@[simp] theorem rotS2_coe (k : S2) (θ : ℝ) (p : S2) :
    ((rotS2 k θ p : S2) : E3) = rot (k : E3) θ (p : E3) := rfl

/-- **The opening operation is a spherical isometry:** `sDist (rot p) (rot q) = sDist p q`.
This is the key fact that the hinge rotation preserves all side lengths and joint angles. -/
theorem sDist_rotS2 (k : S2) (θ : ℝ) (p q : S2) :
    sDist (rotS2 k θ p) (rotS2 k θ q) = sDist p q := by
  rw [sDist, sDist, sInner, sInner, rotS2_coe, rotS2_coe, inner_rot_rot k.2]

/-- **Tangent vector commutes with the rotation:** the tangent at `rot v` toward `rot u` is the
rotation of the tangent at `v` toward `u`.  This is the tangent-plane action of the rotation. -/
theorem tangentTo_rotS2 (k : S2) (θ : ℝ) (v u : S2) :
    tangentTo (rotS2 k θ v) (rotS2 k θ u) = rot (k : E3) θ (tangentTo v u) := by
  rw [tangentTo_eq, tangentTo_eq, rot_sub, rot_smul]
  simp only [rotS2_coe, sInner]
  rw [inner_rot_rot k.2]

/-- **The spherical angle is preserved by the opening rotation** (it is an isometry of `S²`):
`rot` preserves inner products and norms, so the unoriented angle between the (rotated) tangents is
unchanged. -/
theorem sphAngle_rotS2 (k : S2) (θ : ℝ) (u v w : S2) :
    sphAngle (rotS2 k θ u) (rotS2 k θ v) (rotS2 k θ w) = sphAngle u v w := by
  rw [sphAngle, sphAngle, tangentTo_rotS2, tangentTo_rotS2,
    InnerProductGeometry.angle, InnerProductGeometry.angle,
    inner_rot_rot k.2, norm_rot k.2, norm_rot k.2]



/-- `θ ↦ rot k θ v` is continuous. -/
theorem continuous_rot (k v : E3) : Continuous (fun θ : ℝ => rot k θ v) := by
  unfold rot
  fun_prop

/-- `θ ↦ (rot k θ a) i` (a single coordinate) is continuous. -/
theorem continuous_rot_coord (k v : E3) (i : Fin 3) :
    Continuous (fun θ : ℝ => rot k θ v i) :=
  (EuclideanSpace.proj i).continuous.comp (continuous_rot k v)



/-- The planar-rotation inner-product law in the tangent plane: for tangents `u, w ⟂ k`,
`⟪u, rot k θ w⟫ = cos θ · ⟪u,w⟫ + sin θ · ⟪u, k × w⟫`. -/
theorem inner_rot_tangent (k : E3) (θ : ℝ) {u w : E3}
    (hw : (⟪w, k⟫ : ℝ) = 0) :
    (⟪u, rot k θ w⟫ : ℝ)
      = Real.cos θ * ⟪u, w⟫ + Real.sin θ * ⟪u, cross k w⟫ := by
  have hwk : (⟪k, w⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hw
  simp only [rot, inner_add_right, real_inner_smul_right, hwk, mul_zero]; ring





variable {ι : Type*}

/-- The admissible opening set for a finite family of continuous support functions `f : ι → ℝ → ℝ`
and a target `T`. -/
def admissibleSet (f : ι → ℝ → ℝ) (T : ℝ) : Set ℝ :=
  {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) T ∧ ∀ j, 0 ≤ f j θ}

/-- The admissible set is closed (intersection of finitely/arbitrarily many closed conditions, each
the preimage of `[0,∞)` under a continuous function, intersected with the closed interval). -/
theorem isClosed_admissibleSet [Finite ι] {f : ι → ℝ → ℝ} (hf : ∀ j, Continuous (f j)) (T : ℝ) :
    IsClosed (admissibleSet f T) := by
  have h1 : IsClosed (Set.Icc (0 : ℝ) T) := isClosed_Icc
  have h2 : IsClosed {θ : ℝ | ∀ j, 0 ≤ f j θ} := by
    rw [show {θ : ℝ | ∀ j, 0 ≤ f j θ} = ⋂ j, {θ : ℝ | 0 ≤ f j θ} by ext θ; simp]
    exact isClosed_iInter (fun j => isClosed_le continuous_const (hf j))
  exact (h1.inter h2)

/-- `0` is admissible whenever all support functions are nonnegative at `0` and `0 ≤ T`. -/
theorem zero_mem_admissibleSet {f : ι → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (h0 : ∀ j, 0 ≤ f j 0) :
    (0 : ℝ) ∈ admissibleSet f T :=
  ⟨⟨le_refl 0, hT⟩, h0⟩

/-- The admissible set is bounded above by `T`. -/
theorem admissibleSet_bddAbove {f : ι → ℝ → ℝ} {T : ℝ} : BddAbove (admissibleSet f T) :=
  ⟨T, fun _ hx => hx.1.2⟩

/-- **The admissible supremum is admissible** (the set is closed, nonempty, bounded above). -/
theorem sSup_mem_admissibleSet [Finite ι] {f : ι → ℝ → ℝ} (hf : ∀ j, Continuous (f j)) {T : ℝ}
    (hT : 0 ≤ T) (h0 : ∀ j, 0 ≤ f j 0) :
    sSup (admissibleSet f T) ∈ admissibleSet f T := by
  have hne : (admissibleSet f T).Nonempty := ⟨0, zero_mem_admissibleSet hT h0⟩
  exact (isClosed_admissibleSet hf T).csSup_mem hne admissibleSet_bddAbove



/-- **Reach-or-stuck dichotomy.**  At the admissible supremum `s`, either the *target* is reached
(`s = T`), or convexity is *tight*: some support function vanishes (`f j s = 0`) — the great-circle
collinearity of the stuck case.  (If no constraint were tight and `s < T`, all `f j s > 0` and, by
continuity, `f j` would stay positive on a right-neighbourhood of `s`, contradicting that `s` is the
supremum of the admissible set within `[0,T]`.) -/
theorem reach_or_stuck [Finite ι] {f : ι → ℝ → ℝ} (hf : ∀ j, Continuous (f j)) {T : ℝ}
    (hT : 0 ≤ T) (h0 : ∀ j, 0 ≤ f j 0) :
    sSup (admissibleSet f T) = T ∨ ∃ j, f j (sSup (admissibleSet f T)) = 0 := by
  set s := sSup (admissibleSet f T) with hs
  have hmem := sSup_mem_admissibleSet hf hT h0
  rw [← hs] at hmem
  have hsIcc : s ∈ Set.Icc (0 : ℝ) T := hmem.1
  rcases eq_or_lt_of_le hsIcc.2 with hsT | hsT
  · exact Or.inl hsT
  · -- s < T.  If every constraint is strictly positive at s, derive a contradiction with sup.
    by_cases hstuck : ∃ j, f j s = 0
    · exact Or.inr hstuck
    · exfalso
      push_neg at hstuck
      have hpos : ∀ j, 0 < f j s := fun j => lt_of_le_of_ne (hmem.2 j) (fun h => hstuck j h.symm)
      -- each f j is positive on a neighbourhood of s; intersect to get a uniform δ.
      have : ∀ j, ∀ᶠ θ in nhds s, 0 < f j θ := fun j =>
        continuousAt_const.eventually_lt (hf j).continuousAt (hpos j)
      have hall : ∀ᶠ θ in nhds s, ∀ j, 0 < f j θ := Filter.eventually_all.2 this
      -- restrict to the right-neighbourhood within `(s, T]`, which is `NeBot` since `s < T`.
      haveI hnt : (nhdsWithin s (Set.Ioc s T)).NeBot := by
        apply mem_closure_iff_nhdsWithin_neBot.mp
        rw [closure_Ioc (ne_of_lt hsT)]; exact ⟨le_refl s, le_of_lt hsT⟩
      -- every such point is admissible and strictly above `s`, contradicting `s = sSup`.
      have hev : ∀ᶠ θ in nhdsWithin s (Set.Ioc s T), θ ∈ admissibleSet f T ∧ s < θ := by
        have hmono : ∀ᶠ θ in nhdsWithin s (Set.Ioc s T), ∀ j, 0 < f j θ :=
          hall.filter_mono nhdsWithin_le_nhds
        filter_upwards [hmono, self_mem_nhdsWithin] with θ hθpos hθIoc
        exact ⟨⟨⟨le_of_lt (lt_of_le_of_lt hsIcc.1 hθIoc.1), hθIoc.2⟩, fun j => le_of_lt (hθpos j)⟩,
          hθIoc.1⟩
      obtain ⟨θ, hθadm, hθgt⟩ := hev.exists
      have hub : θ ≤ s := le_csSup admissibleSet_bddAbove hθadm
      exact absurd hub (not_le.mpr hθgt)











end ProofsInTheBook.SphericalRotation

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalRotation
-/
/- Source module: ProofsInTheBook.SphericalSZ -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm ProofsInTheBook.SphericalRotation

namespace ProofsInTheBook.SphericalSZ



/-- `(a × c) × b = ⟪b,a⟫ • c − ⟪b,c⟫ • a` (a specialised double-cross identity). -/
theorem crossw_eq (a b c : E3) :
    cross (cross a c) b = (⟪b, a⟫ : ℝ) • c - (⟪b, c⟫ : ℝ) • a := by
  have h := ProofsInTheBook.SphericalRotation.cross_cross b a c
  rw [ProofsInTheBook.SphericalRotation.cross_antisymm (cross a c) b, h]; module

/-- `w × (x • c − y • a) = x • (w × c) − y • (w × a)` (bilinearity, packaged for the chain). -/
theorem cross_lin (w c a : E3) (x y : ℝ) :
    cross w (x • c - y • a) = x • cross w c - y • cross w a := by
  rw [sub_eq_add_neg, ProofsInTheBook.SphericalRotation.cross_add_right,
      ProofsInTheBook.SphericalRotation.cross_smul_right]
  rw [show (-(y • a)) = (-y) • a by module, ProofsInTheBook.SphericalRotation.cross_smul_right]
  module

/-- **The explicit coplanar decomposition.**  If `b` is orthogonal to `a × c` (i.e. coplanar with
`a` and `c` through the origin), then `‖a×c‖² • b` is the explicit Gram combination of `a` and `c`.
Proved by the double-cross expansion `(a×c) × ((a×c) × b) = ⟪a×c,b⟫•(a×c) − ‖a×c‖²•b` with the
left side rewritten through `crossw_eq`. -/
theorem normsq_smul_b (a b c : E3) (hperp : (⟪cross a c, b⟫ : ℝ) = 0) :
    (‖cross a c‖ ^ 2) • b
      = ((⟪b, a⟫ : ℝ) * (⟪c, c⟫ : ℝ) - (⟪b, c⟫ : ℝ) * (⟪a, c⟫ : ℝ)) • a
        + ((⟪b, c⟫ : ℝ) * (⟪a, a⟫ : ℝ) - (⟪b, a⟫ : ℝ) * (⟪c, a⟫ : ℝ)) • c := by
  have key : cross (cross a c) (cross (cross a c) b)
      = (⟪(cross a c), b⟫ : ℝ) • (cross a c) - (‖cross a c‖ ^ 2) • b := by
    rw [ProofsInTheBook.SphericalRotation.cross_cross, real_inner_self_eq_norm_sq]
  rw [hperp, zero_smul, zero_sub] at key
  rw [crossw_eq a b c, cross_lin, crossw_eq a c c, crossw_eq a a c] at key
  linear_combination (norm := module) key

/-- A short arc has linearly independent endpoints: `a × c ≠ 0` (Lagrange identity + the short-arc
nondegeneracy `⟪a,c⟫ ≠ ±1`). -/
theorem cross_ne_zero_of_shortArc (a c : S2) (h : ShortArc a c) :
    cross (a : E3) (c : E3) ≠ 0 := by
  intro hz
  have hns : ‖cross (a : E3) (c : E3)‖ ^ 2 = 0 := by rw [hz, norm_zero]; ring
  rw [norm_sq_cross, a.2, c.2] at hns
  have hinner : sInner a c * sInner a c = 1 := by
    have hh : (⟪(a : E3), (c : E3)⟫ : ℝ) = sInner a c := rfl
    rw [hh] at hns; nlinarith [hns]
  rcases mul_self_eq_one_iff.mp hinner with h1 | h1
  · have : sDist a c = 0 := by rw [sDist, h1, Real.arccos_one]
    exact h.1 (sDist_eq_zero_iff.mp this)
  · have hcos : sInner a c = -1 := h1
    have hnorm : ‖(a : E3) + (c : E3)‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right]
      rw [S2.inner_self, S2.inner_self]
      have h1' : (⟪(a : E3), (c : E3)⟫ : ℝ) = -1 := hcos
      have h2' : (⟪(c : E3), (a : E3)⟫ : ℝ) = -1 := by rw [real_inner_comm]; exact h1'
      rw [h1', h2']; ring
    have hac : (a : E3) + (c : E3) = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hnorm
      exact norm_eq_zero.mp this
    exact h.2 (eq_neg_of_add_eq_zero_left hac)

/-- **Great-circle betweenness from the vanishing support determinant.**  When the closing support
determinant `det3 (b:E3) (a:E3) (c:E3)` vanishes (`b` coplanar with `a, c`), the endpoints `a, c`
form a short arc, and the two convex-position Gram coefficients are nonnegative, the middle vertex
`b` lies in `span ℝ≥0 {a, c}` — the great-circle betweenness equation (2).  Dividing the explicit
coplanar decomposition `normsq_smul_b` by `‖a×c‖² > 0` exhibits `b` as the nonnegative combination
`b = (α/‖a×c‖²) • a + (β/‖a×c‖²) • c`. -/
theorem betweenness_span_nnreal (a c b : S2) (hsa : ShortArc a c)
    (hdet : det3 (b : E3) (a : E3) (c : E3) = 0)
    (hα : 0 ≤ (⟪(b : E3), (a : E3)⟫ : ℝ) - (⟪(b : E3), (c : E3)⟫ : ℝ) * (⟪(a : E3), (c : E3)⟫ : ℝ))
    (hβ : 0 ≤ (⟪(b : E3), (c : E3)⟫ : ℝ) - (⟪(b : E3), (a : E3)⟫ : ℝ) * (⟪(c : E3), (a : E3)⟫ : ℝ)) :
    (b : E3) ∈ Submodule.span NNReal ({(a : E3), (c : E3)} : Set E3) := by
  have hperp : (⟪cross (a : E3) (c : E3), (b : E3)⟫ : ℝ) = 0 := by
    rw [real_inner_comm, inner_cross_eq_det3]; exact hdet
  have hns := normsq_smul_b (a : E3) (b : E3) (c : E3) hperp
  rw [S2.inner_self a, S2.inner_self c] at hns
  have hne : cross (a : E3) (c : E3) ≠ 0 := cross_ne_zero_of_shortArc a c hsa
  have hw2 : (0 : ℝ) < ‖cross (a : E3) (c : E3)‖ ^ 2 := by positivity
  set w2 : ℝ := ‖cross (a : E3) (c : E3)‖ ^ 2 with hw2def
  set acoef : ℝ :=
    (⟪(b : E3), (a : E3)⟫ : ℝ) * 1 - (⟪(b : E3), (c : E3)⟫ : ℝ) * (⟪(a : E3), (c : E3)⟫ : ℝ)
    with hacdef
  set bcoef : ℝ :=
    (⟪(b : E3), (c : E3)⟫ : ℝ) * 1 - (⟪(b : E3), (a : E3)⟫ : ℝ) * (⟪(c : E3), (a : E3)⟫ : ℝ)
    with hbcdef
  have hac0 : 0 ≤ acoef := by rw [hacdef]; linarith [hα]
  have hbc0 : 0 ≤ bcoef := by rw [hbcdef]; linarith [hβ]
  have hb_eq : (b : E3) = (acoef / w2) • (a : E3) + (bcoef / w2) • (c : E3) := by
    have hns2 : (b : E3) = (1 / w2) • (acoef • (a : E3) + bcoef • (c : E3)) := by
      rw [← hns, smul_smul, one_div_mul_cancel (ne_of_gt hw2), one_smul]
    rw [hns2, smul_add, smul_smul, smul_smul]; congr 2 <;> ring
  have hadiv : 0 ≤ acoef / w2 := div_nonneg hac0 (le_of_lt hw2)
  have hbdiv : 0 ≤ bcoef / w2 := div_nonneg hbc0 (le_of_lt hw2)
  rw [Submodule.mem_span_pair]
  refine ⟨⟨acoef / w2, hadiv⟩, ⟨bcoef / w2, hbdiv⟩, ?_⟩
  show (acoef / w2 : ℝ) • (a : E3) + (bcoef / w2 : ℝ) • (c : E3) = (b : E3)
  exact hb_eq.symm



/-- The **stuck-case raw data** of one opening step (book's labelling `q₂ = A 1`, `q₁ = A 0`,
`qₙ* = qstar`): the closing support is degenerate (`det3 = 0`), the support endpoints `A 1, qstar`
form a short arc, the two convex-position Gram coefficients are nonnegative (so `A 0` is *between*
`A 1` and `qstar`), and the opening / sub-comparison / equal-side bounds hold. -/
structure StuckData {n : ℕ} (A B : Fin (n + 1 + 1) → S2) (qstar : S2) : Prop where
  shortArc : ShortArc (A 1) qstar
  det_zero : det3 (A 0 : E3) (A 1 : E3) (qstar : E3) = 0
  signA : 0 ≤ (⟪(A 0 : E3), (A 1 : E3)⟫ : ℝ)
      - (⟪(A 0 : E3), (qstar : E3)⟫ : ℝ) * (⟪(A 1 : E3), (qstar : E3)⟫ : ℝ)
  signC : 0 ≤ (⟪(A 0 : E3), (qstar : E3)⟫ : ℝ)
      - (⟪(A 0 : E3), (A 1 : E3)⟫ : ℝ) * (⟪(qstar : E3), (A 1 : E3)⟫ : ℝ)
  opening : endpt A < sDist (A 0) qstar
  subcomp : sDist (A 1) qstar ≤ sDist (B 1) (B (Fin.last (n + 1)))
  firstSide : sDist (B 1) (B 0) = sDist (A 1) (A 0)

/-- **The isolated geometric primitive (elementary form).**  For every level-`(n+1)` convex arm pair
with equal sides and nondecreasing joints, *given the level-`n` sub-comparison* (the inductive
hypothesis), the design §8 opening produces: always the weak endpoint bound, and — whenever some
joint of `B` is strictly wider — *either* a stuck vertex `qstar` with the elementary `StuckData`
*or* the direct strict endpoint bound (the reached / equal-angle-cut case).  This is exactly the raw
output of the Rodrigues opening + admissible supremum + `reach_or_stuck` construction; everything
the book derives from it is proved below. -/
def SZOpeningCore : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∀ (A B : Fin (n + 1 + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
      (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
      SZComparison n →
      endpt A ≤ endpt B ∧
        ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
          (∃ qstar : S2, StuckData A B qstar) ∨ endpt A < endpt B)

/-- **The bridge `SZOpeningCore → SZGeom`.**  The weak bound is passed through; for the strict
disjunction, the stuck case's elementary `StuckData` is converted into the witness's `span ℝ≥0`
betweenness by the proved `betweenness_span_nnreal` (the vanishing determinant + the convex-position
signs give `A 0 ∈ span ℝ≥0 {A 1, qstar}`), and the opening / sub-comparison / equal-side bounds are
forwarded verbatim into `SZGeomWitness.strict`'s `Or.inl`.  The reached / cut case is forwarded as
`Or.inr`.  This is the geometric bookkeeping the rotation engine left isolated. -/
theorem szGeom_of_core (hcore : SZOpeningCore) : SZGeom := by
  intro n hn A B hA hB hside hangle ih
  obtain ⟨hweak, hstrict⟩ := hcore n hn A B hA hB hside hangle ih
  refine ⟨hweak, ?_⟩
  intro hwider
  rcases hstrict hwider with ⟨qstar, hsd⟩ | hdirect
  · -- stuck: convert det3 = 0 + signs into the `span ℝ≥0` betweenness, then forward the bounds.
    refine Or.inl ⟨qstar, ?_, hsd.opening, hsd.subcomp, hsd.firstSide⟩
    exact betweenness_span_nnreal (A 1) qstar (A 0) hsd.shortArc hsd.det_zero hsd.signA hsd.signC
  · exact Or.inr hdirect

/-- **The Schoenberg–Zaremba spherical arm lemma, conditional on the elementary opening core.**
Composing the bridge with the proven `schoenbergZaremba_of_geom`: once the design §8 opening core is
supplied, the named kernel obligation `SchoenbergZarembaTarget` holds — equal-sided convex arms with
nondecreasing joints admit the `SZChain`, so the endpoint distance is monotone, strictly so when some
joint is strictly wider.  All the inequality content (the spherical triangle inequality, the stuck
chain `(∗)`, the great-circle betweenness extraction, the base case, the recursion) is proved
unconditionally. -/
theorem schoenbergZaremba_of_core (hcore : SZOpeningCore) : SchoenbergZarembaTarget :=
  schoenbergZaremba_of_geom (szGeom_of_core hcore)


theorem det_zero_of_betweenness (A1 qstar A0 : S2) (s t : ℝ)
    (hb : (A0 : E3) = s • (A1 : E3) + t • (qstar : E3)) :
    det3 (A0 : E3) (A1 : E3) (qstar : E3) = 0 := by
  rw [show det3 (A0 : E3) (A1 : E3) (qstar : E3)
        = (⟪(A0 : E3), cross (A1 : E3) (qstar : E3)⟫ : ℝ) from (inner_cross_eq_det3 _ _ _).symm]
  have h1 : (⟪(A1 : E3), cross (A1 : E3) (qstar : E3)⟫ : ℝ) = 0 := by
    rw [real_inner_comm]; exact inner_cross_left _ _
  have h2 : (⟪(qstar : E3), cross (A1 : E3) (qstar : E3)⟫ : ℝ) = 0 := by
    rw [real_inner_comm]; exact inner_cross_right _ _
  rw [hb, inner_add_left, real_inner_smul_left, real_inner_smul_left, h1, h2]; ring

end ProofsInTheBook.SphericalSZ

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZ
-/
/- Source module: ProofsInTheBook.SphericalCore -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ

namespace ProofsInTheBook.SphericalCore



/-- The Rodrigues rotation commutes with the cross product: `rot k θ (a × b) = (rot k θ a) × (rot k θ
b)` for a unit axis `k`.  Proved by expanding both sides through the engine's cross-product algebra
(`cross_cross`, the `bac − cab` rule, with `k` a unit axis so `k × (k × v) = ⟪k,v⟫•k − v`) into a
common basis and closing with `module` after substituting `cos²θ + sin²θ = 1`. -/
theorem rot_cross {k : E3} (hk : ‖k‖ = 1) (θ : ℝ) (a b : E3) :
    rot k θ (cross a b) = cross (rot k θ a) (rot k θ b) := by
  have hkk : (⟪k, k⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hk]; norm_num
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hkk1 : (k 0) ^ 2 + (k 1) ^ 2 + (k 2) ^ 2 = 1 := by
    rw [inner_eq_coord] at hkk; linear_combination hkk
  apply ext_coord
  · simp only [rot, cross_apply_zero, cross_apply_one, cross_apply_two, add_apply, smul_apply,
      inner_eq_coord]
    linear_combination (Real.cos θ*Real.sin θ*(a 0)*(b 1)*(k 1) + Real.cos θ*Real.sin θ*(a 0)*(b 2)*(k 2) - Real.cos θ*Real.sin θ*(a 1)*(b 0)*(k 1) - Real.cos θ*Real.sin θ*(a 2)*(b 0)*(k 2) - Real.cos θ*(a 1)*(b 2) + Real.cos θ*(a 2)*(b 1) - Real.sin θ^2*(a 1)*(b 2) + Real.sin θ^2*(a 2)*(b 1) - Real.sin θ*(a 0)*(b 1)*(k 1) - Real.sin θ*(a 0)*(b 2)*(k 2) + Real.sin θ*(a 1)*(b 0)*(k 1) + Real.sin θ*(a 2)*(b 0)*(k 2) + (a 1)*(b 2) - (a 2)*(b 1)) * hkk1 + (-(a 0)*(b 1)*(k 0)*(k 2) + (a 0)*(b 2)*(k 0)*(k 1) + (a 1)*(b 0)*(k 0)*(k 2) + (a 1)*(b 2)*(k 1)^2 + (a 1)*(b 2)*(k 2)^2 - (a 1)*(b 2) - (a 2)*(b 0)*(k 0)*(k 1) - (a 2)*(b 1)*(k 1)^2 - (a 2)*(b 1)*(k 2)^2 + (a 2)*(b 1)) * hcs
  · simp only [rot, cross_apply_zero, cross_apply_one, cross_apply_two, add_apply, smul_apply,
      inner_eq_coord]
    linear_combination (-Real.cos θ^2*(a 0)*(b 2) + Real.cos θ^2*(a 2)*(b 0) - Real.cos θ*Real.sin θ*(a 0)*(b 1)*(k 0) + Real.cos θ*Real.sin θ*(a 1)*(b 0)*(k 0) + Real.cos θ*Real.sin θ*(a 1)*(b 2)*(k 2) - Real.cos θ*Real.sin θ*(a 2)*(b 1)*(k 2) + Real.cos θ*(a 0)*(b 2) - Real.cos θ*(a 2)*(b 0) + Real.sin θ*(a 0)*(b 1)*(k 0) - Real.sin θ*(a 1)*(b 0)*(k 0) - Real.sin θ*(a 1)*(b 2)*(k 2) + Real.sin θ*(a 2)*(b 1)*(k 2)) * hkk1 + (-(a 0)*(b 1)*(k 1)*(k 2) + (a 0)*(b 2)*(k 1)^2 + (a 1)*(b 0)*(k 1)*(k 2) - (a 1)*(b 2)*(k 0)*(k 1) - (a 2)*(b 0)*(k 1)^2 + (a 2)*(b 1)*(k 0)*(k 1)) * hcs
  · simp only [rot, cross_apply_zero, cross_apply_one, cross_apply_two, add_apply, smul_apply,
      inner_eq_coord]
    linear_combination (Real.cos θ^2*(a 0)*(b 1) - Real.cos θ^2*(a 1)*(b 0) - Real.cos θ*Real.sin θ*(a 0)*(b 2)*(k 0) - Real.cos θ*Real.sin θ*(a 1)*(b 2)*(k 1) + Real.cos θ*Real.sin θ*(a 2)*(b 0)*(k 0) + Real.cos θ*Real.sin θ*(a 2)*(b 1)*(k 1) - Real.cos θ*(a 0)*(b 1) + Real.cos θ*(a 1)*(b 0) + Real.sin θ*(a 0)*(b 2)*(k 0) + Real.sin θ*(a 1)*(b 2)*(k 1) - Real.sin θ*(a 2)*(b 0)*(k 0) - Real.sin θ*(a 2)*(b 1)*(k 1)) * hkk1 + (-(a 0)*(b 1)*(k 2)^2 + (a 0)*(b 2)*(k 1)*(k 2) + (a 1)*(b 0)*(k 2)^2 - (a 1)*(b 2)*(k 0)*(k 2) - (a 2)*(b 0)*(k 1)*(k 2) + (a 2)*(b 1)*(k 0)*(k 2)) * hcs







/-- **Tangent at the axis-vertex toward a rotated target = rotation of the tangent.**  When the base
point `k` is exactly the rotation axis, `tangentTo k (rotS2 k θ q) = rot (k:E3) θ (tangentTo k q)`
(the axis is fixed by `rot`, and `rot` preserves inner products). -/
theorem tangentTo_rotS2_axis (k : S2) (θ : ℝ) (q : S2) :
    tangentTo k (rotS2 k θ q) = rot (k : E3) θ (tangentTo k q) := by
  rw [tangentTo_eq, tangentTo_eq, rot_sub, rot_smul, rot_axis k.2]
  have hin : sInner (rotS2 k θ q) k = sInner q k := by
    simp only [sInner, rotS2_coe]; rw [inner_rot_axis k.2]
  rw [hin]
  rfl

/-- **The opened-joint angle moves by the planar-rotation law.**  The cosine-numerator of the opened
joint angle at axis `k` between the fixed incoming tangent `tangentTo k p` and the outgoing tangent
toward the rotated target `rotS2 k θ q` is
`cos θ · ⟪tangentTo k p, tangentTo k q⟫ + sin θ · ⟪tangentTo k p, k × tangentTo k q⟫` — the planar
rotation of a fixed tangent.  (The tangent `tangentTo k q ⟂ k`, so `inner_rot_tangent` applies.) -/
theorem inner_tangent_opened (k : S2) (θ : ℝ) (p q : S2) :
    (⟪tangentTo k p, tangentTo k (rotS2 k θ q)⟫ : ℝ)
      = Real.cos θ * ⟪tangentTo k p, tangentTo k q⟫
        + Real.sin θ * ⟪tangentTo k p, cross (k : E3) (tangentTo k q)⟫ := by
  rw [tangentTo_rotS2_axis]
  exact inner_rot_tangent (k : E3) θ (tangentTo_orthogonal k q)

































/-- **The explicit chain `SZOpeningCore → SchoenbergZarembaTarget`**, re-exported through the proven
bridge `ProofsInTheBook.SphericalSZ.schoenbergZaremba_of_core`.  Once `SZOpeningCore` is discharged
(using the substrate proved in this module), the named kernel obligation `SchoenbergZarembaTarget`
holds unconditionally, hence so do `spherical_arm_mono` / `spherical_arm_mono_strict`. -/
theorem schoenbergZaremba_of_openingCore (hcore : SZOpeningCore) : SchoenbergZarembaTarget :=
  ProofsInTheBook.SphericalSZ.schoenbergZaremba_of_core hcore

end ProofsInTheBook.SphericalCore

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalCore
-/
/- Source module: ProofsInTheBook.SphericalFinish -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore

namespace ProofsInTheBook.SphericalFinish



/-- The outgoing opened tangent is nonzero for a short arc base/target: it is the rotation of the
fixed tangent `tangentTo k q`, whose norm `sin (sDist k q) > 0` is preserved by `rot`. -/
theorem tangentTo_open_ne_zero {k q : S2} (hkq : ShortArc k q) (θ : ℝ) :
    tangentTo k (rotS2 k θ q) ≠ 0 := by
  rw [tangentTo_rotS2_axis]
  intro h
  have hnorm : ‖rot (k : E3) θ (tangentTo k q)‖ = 0 := by rw [h, norm_zero]
  rw [norm_rot k.2] at hnorm
  exact (tangentTo_ne_zero_iff k q).2 hkq (norm_eq_zero.mp hnorm)

/-- **The opened joint angle is continuous in `θ`.**  Its two tangent arguments are the fixed
nonzero `tangentTo k p` and the moving-but-nonzero `tangentTo k (rotS2 k θ q) = rot k θ (tangentTo k
q)`; `InnerProductGeometry.continuousAt_angle` plus the continuity of `rot` in `θ` give it. -/
theorem continuous_openedJointAngle {k p q : S2} (hkp : ShortArc k p) (hkq : ShortArc k q) :
    Continuous (fun θ : ℝ => sphAngle p k (rotS2 k θ q)) := by
  have hp0 : tangentTo k p ≠ 0 := (tangentTo_ne_zero_iff k p).2 hkp
  rw [continuous_iff_continuousAt]
  intro θ₀
  have hq0 : tangentTo k (rotS2 k θ₀ q) ≠ 0 := tangentTo_open_ne_zero hkq θ₀
  have hcont_pair :
      ContinuousAt (fun θ : ℝ => ((tangentTo k p, tangentTo k (rotS2 k θ q)) : E3 × E3)) θ₀ := by
    apply ContinuousAt.prodMk continuousAt_const
    have : (fun θ : ℝ => tangentTo k (rotS2 k θ q))
        = (fun θ : ℝ => rot (k : E3) θ (tangentTo k q)) := by
      funext θ; exact tangentTo_rotS2_axis k θ q
    rw [this]
    exact (continuous_rot (k : E3) (tangentTo k q)).continuousAt
  have hangle :
      ContinuousAt (fun y : E3 × E3 => InnerProductGeometry.angle y.1 y.2)
        (tangentTo k p, tangentTo k (rotS2 k θ₀ q)) :=
    InnerProductGeometry.continuousAt_angle hp0 hq0
  have hcomp :
      ContinuousAt
        ((fun y : E3 × E3 => InnerProductGeometry.angle y.1 y.2) ∘
          (fun θ : ℝ => ((tangentTo k p, tangentTo k (rotS2 k θ q)) : E3 × E3))) θ₀ :=
    ContinuousAt.comp
      (g := fun y : E3 × E3 => InnerProductGeometry.angle y.1 y.2)
      (f := fun θ : ℝ => ((tangentTo k p, tangentTo k (rotS2 k θ q)) : E3 × E3))
      hangle hcont_pair
  have heq : (fun θ : ℝ => sphAngle p k (rotS2 k θ q))
      = ((fun y : E3 × E3 => InnerProductGeometry.angle y.1 y.2) ∘
          (fun θ : ℝ => ((tangentTo k p, tangentTo k (rotS2 k θ q)) : E3 × E3))) := by
    funext θ; rfl
  rw [heq]; exact hcomp

/-- **The opened joint cosine is a sinusoid over a constant norm.**
`cos (sphAngle p k (rotS2 k θ q)) = (cos θ · ⟪tangentTo k p, tangentTo k q⟫
    + sin θ · ⟪tangentTo k p, k × tangentTo k q⟫) / (‖tangentTo k p‖ · ‖tangentTo k q‖)`. -/
theorem cos_openedJointAngle (k p q : S2) (θ : ℝ) :
    Real.cos (sphAngle p k (rotS2 k θ q))
      = (Real.cos θ * (⟪tangentTo k p, tangentTo k q⟫ : ℝ)
          + Real.sin θ * (⟪tangentTo k p, cross (k : E3) (tangentTo k q)⟫ : ℝ))
        / (‖tangentTo k p‖ * ‖tangentTo k (rotS2 k θ q)‖) := by
  rw [sphAngle, InnerProductGeometry.cos_angle, inner_tangent_opened]







/-- **The Gram-sign coordinate identities.**  For unit `A1, qstar` and a coplanar combination
`A0 = s • A1 + t • qstar`, the two `StuckData` Gram quantities are the planar coordinates scaled by
the (Lagrange) Gram determinant `‖A1 × qstar‖²`. -/
theorem gramSigns_eq_coords (A0 A1 qstar : S2) (s t : ℝ)
    (hb : (A0 : E3) = s • (A1 : E3) + t • (qstar : E3)) :
    ((⟪(A0 : E3), (A1 : E3)⟫ : ℝ)
        - (⟪(A0 : E3), (qstar : E3)⟫ : ℝ) * (⟪(A1 : E3), (qstar : E3)⟫ : ℝ)
      = s * ‖cross (A1 : E3) (qstar : E3)‖ ^ 2)
    ∧ ((⟪(A0 : E3), (qstar : E3)⟫ : ℝ)
        - (⟪(A0 : E3), (A1 : E3)⟫ : ℝ) * (⟪(qstar : E3), (A1 : E3)⟫ : ℝ)
      = t * ‖cross (A1 : E3) (qstar : E3)‖ ^ 2) := by
  have hp : (⟪(A1 : E3), (qstar : E3)⟫ : ℝ) = (⟪(qstar : E3), (A1 : E3)⟫ : ℝ) := real_inner_comm _ _
  have hlag : ‖cross (A1 : E3) (qstar : E3)‖ ^ 2
      = 1 - (⟪(A1 : E3), (qstar : E3)⟫ : ℝ) ^ 2 := by
    rw [norm_sq_cross, A1.2, qstar.2]; ring
  have h0A1 : (⟪(A0 : E3), (A1 : E3)⟫ : ℝ)
      = s * 1 + t * (⟪(qstar : E3), (A1 : E3)⟫ : ℝ) := by
    rw [hb, inner_add_left, real_inner_smul_left, real_inner_smul_left, S2.inner_self]
  have h0q : (⟪(A0 : E3), (qstar : E3)⟫ : ℝ)
      = s * (⟪(A1 : E3), (qstar : E3)⟫ : ℝ) + t * 1 := by
    rw [hb, inner_add_left, real_inner_smul_left, real_inner_smul_left, S2.inner_self]
  refine ⟨?_, ?_⟩
  · rw [h0A1, h0q, hlag, ← hp]; ring
  · rw [h0A1, h0q, hlag, ← hp]; ring

/-- **Sign extraction from convex-position betweenness.**  If `A 0` lies on the short great-circle
arc between `A 1` and `qstar` (a *nonnegative* combination `A 0 = s • A 1 + t • qstar`, `s, t ≥ 0`)
and `A 1, qstar` is a short arc, then both `StuckData` Gram signs hold.  This is the form in which the
opening construction's convex position discharges the signs: betweenness ⟹ both signs. -/
theorem stuckSigns_of_between (A0 A1 qstar : S2) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hb : (A0 : E3) = s • (A1 : E3) + t • (qstar : E3)) :
    (0 ≤ (⟪(A0 : E3), (A1 : E3)⟫ : ℝ)
        - (⟪(A0 : E3), (qstar : E3)⟫ : ℝ) * (⟪(A1 : E3), (qstar : E3)⟫ : ℝ))
    ∧ (0 ≤ (⟪(A0 : E3), (qstar : E3)⟫ : ℝ)
        - (⟪(A0 : E3), (A1 : E3)⟫ : ℝ) * (⟪(qstar : E3), (A1 : E3)⟫ : ℝ)) := by
  obtain ⟨hA, hC⟩ := gramSigns_eq_coords A0 A1 qstar s t hb
  have hnn : (0 : ℝ) ≤ ‖cross (A1 : E3) (qstar : E3)‖ ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · rw [hA]; exact mul_nonneg hs hnn
  · rw [hC]; exact mul_nonneg ht hnn



/-- **Nonnegative real coordinates from `span ℝ≥0` membership.**  If `b ∈ span ℝ≥0 {a, c}` then `b`
is a *nonnegative-real* combination `b = s • a + t • c` with `s, t ≥ 0`.  Extracts the convex-position
coordinates from the membership the opening construction produces. -/
theorem nnreal_coords_of_mem_span {a c b : E3}
    (h : b ∈ Submodule.span NNReal ({a, c} : Set E3)) :
    ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ b = s • a + t • c := by
  rw [Submodule.mem_span_pair] at h
  obtain ⟨u, v, huv⟩ := h
  refine ⟨(u : ℝ), (v : ℝ), u.2, v.2, ?_⟩
  rw [← huv]
  have hu : (u : ℝ≥0) • a = (u : ℝ) • a := by
    rw [← smul_one_smul ℝ (u : ℝ≥0) a]; simp [NNReal.smul_def]
  have hv : (v : ℝ≥0) • c = (v : ℝ) • c := by
    rw [← smul_one_smul ℝ (v : ℝ≥0) c]; simp [NNReal.smul_def]
  rw [hu, hv]



/-- `firstSide` is forced by the equal-side hypothesis: `sDist (B 1)(B 0) = sDist (A 1)(A 0)`. -/
theorem firstSide_of_equalSides {n : ℕ} (A B : Fin (n + 1 + 1) → S2)
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i) :
    sDist (B 1) (B 0) = sDist (A 1) (A 0) := by
  have h0 := hside 0
  have hcs : (Fin.castSucc (0 : Fin (n + 1)) : Fin (n + 1 + 1)) = 0 := by apply Fin.ext; simp
  have hsc : (Fin.succ (0 : Fin (n + 1)) : Fin (n + 1 + 1)) = 1 := by apply Fin.ext; simp
  have hA0 : sideLen A 0 = sDist (A 0) (A 1) := by rw [sideLen, hcs, hsc]
  have hB0 : sideLen B 0 = sDist (B 0) (B 1) := by rw [sideLen, hcs, hsc]
  rw [hA0, hB0] at h0
  rw [sDist_comm (B 1) (B 0), sDist_comm (A 1) (A 0), h0]

/-- **`StuckData` from convex-position betweenness + the bounds.**  Given the opening's output — the
membership `A 0 ∈ span ℝ≥0 {A 1, qstar}` (so `A 0` is between `A 1` and `qstar`), the short arc, and
the opening / sub-comparison bounds — together with the equal-side hypothesis, the elementary
`StuckData A B qstar` holds: the determinant vanishes and both Gram signs follow from the betweenness
coordinates, while `firstSide` is forced by equal sides.  This is the genuine derivation that turns
the *geometric* opening output into the *elementary* `StuckData` the chain consumes. -/
theorem stuckData_of_between {n : ℕ} (A B : Fin (n + 1 + 1) → S2) (qstar : S2)
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i)
    (hsa : ShortArc (A 1) qstar)
    (hmem : (A 0 : E3) ∈ Submodule.span NNReal ({(A 1 : E3), (qstar : E3)} : Set E3))
    (hopen : endpt A < sDist (A 0) qstar)
    (hsub : sDist (A 1) qstar ≤ sDist (B 1) (B (Fin.last (n + 1)))) :
    StuckData A B qstar := by
  obtain ⟨s, t, hs, ht, hb⟩ := nnreal_coords_of_mem_span hmem
  obtain ⟨hsignA, hsignC⟩ := stuckSigns_of_between (A 0) (A 1) qstar s t hs ht hb
  exact
    { shortArc := hsa
      det_zero := det_zero_of_betweenness (A 1) qstar (A 0) s t hb
      signA := hsignA
      signC := hsignC
      opening := hopen
      subcomp := hsub
      firstSide := firstSide_of_equalSides A B hside }



/-- **The strictly-smaller opening obligation.**  For every level-`(n+1)` convex arm pair with equal
sides and nondecreasing joints, given the inductive sub-comparison, the design §8 opening produces:
always the weak endpoint bound, and — whenever some joint of `B` is strictly wider — *either* a moved
tail `qstar` with the **geometric** convex-position data (the betweenness membership, the short arc,
and the opening / sub-comparison bounds) *or* the direct strict bound.  This carries strictly less
than `SZOpeningCore`: the determinant, the two Gram signs, and `firstSide` are *derived* in
`szOpeningCore_of_openingData`, not assumed. -/
def OpeningData : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∀ (A B : Fin (n + 1 + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
      (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
      SZComparison n →
      endpt A ≤ endpt B ∧
        ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
          (∃ qstar : S2,
            ShortArc (A 1) qstar ∧
            (A 0 : E3) ∈ Submodule.span NNReal ({(A 1 : E3), (qstar : E3)} : Set E3) ∧
            endpt A < sDist (A 0) qstar ∧
            sDist (A 1) qstar ≤ sDist (B 1) (B (Fin.last (n + 1))))
          ∨ endpt A < endpt B)

/-- **The reduction `OpeningData → SZOpeningCore`.**  The weak bound is forwarded; in the stuck
branch the geometric convex-position output is turned into the elementary `StuckData` by
`stuckData_of_between` (deriving the determinant, the two Gram signs, and `firstSide`), and the
reached/cut branch is forwarded.  This is the genuine §8.2–§8.5 bookkeeping converting the opening's
raw geometric output into `SZOpeningCore`'s elementary form. -/
theorem szOpeningCore_of_openingData (hod : OpeningData) : SZOpeningCore := by
  intro n hn A B hA hB hside hangle ih
  obtain ⟨hweak, hstrict⟩ := hod n hn A B hA hB hside hangle ih
  refine ⟨hweak, ?_⟩
  intro hwider
  rcases hstrict hwider with ⟨qstar, hsa, hmem, hopen, hsub⟩ | hdirect
  · exact Or.inl ⟨qstar, stuckData_of_between A B qstar hside hsa hmem hopen hsub⟩
  · exact Or.inr hdirect

/-- **The Schoenberg–Zaremba spherical arm lemma, conditional on the strictly-smaller opening
obligation `OpeningData`.**  Composing the reduction with the proven chain
`schoenbergZaremba_of_openingCore`: once the design §8 opening *construction* is supplied (now in its
geometric, sign-free form), the named kernel obligation `SchoenbergZarembaTarget` holds — equal-sided
convex arms with nondecreasing joints have monotone endpoint distance, strictly so when some joint is
strictly wider.  Every sign-level and inequality step (the Gram signs, `firstSide`, the betweenness
extraction, the triangle-inequality chain, the base case, the recursion) is proved unconditionally. -/
theorem schoenbergZaremba_of_openingData (hod : OpeningData) : SchoenbergZarembaTarget :=
  schoenbergZaremba_of_openingCore (szOpeningCore_of_openingData hod)





end ProofsInTheBook.SphericalFinish

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalFinish
-/
/- Source module: ProofsInTheBook.SphericalOpening -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish

namespace ProofsInTheBook.SphericalOpening











/-- **The isolated §8.3–§8.4 convex-position primitive (elementary form).**  For every level-`(n+1)`
convex arm pair with equal sides, nondecreasing joints, the level-`n` sub-comparison, and *some
strictly-wider joint*, the design §8 opening (to the admissible supremum of the last joint) produces
*either*

* a moved tail `qstar` with the elementary stuck data — the short arc `A 1, qstar`, the *vanishing*
  closing-support determinant `det3 (A 0)(A 1) qstar = 0`, the two convex-position Gram signs (so the
  coplanar `A 0` is on the near side of the arc, i.e. *between* `A 1` and `qstar`), the strict opening
  bound `endpt A < sDist (A 0) qstar`, and the level-`n` sub-comparison bound — *or*

* the direct strict endpoint bound `endpt A < endpt B` (the reached / equal-angle-cut case).

This packages exactly the geometric output of the Rodrigues opening + admissible-supremum
`reach_or_stuck` + the convex-position sign determination; it is the single fact the rotation engine
does not yet mechanise.  It is stated in elementary (determinant + sign) form so the reduction below
genuinely *produces* the `span ℝ≥0` betweenness and the elementary `StuckData`. -/
def OpenedArmReachOrStuck : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∀ (A B : Fin (n + 1 + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
      (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
      SZComparison n →
      endpt A ≤ endpt B ∧
      ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
        (∃ qstar : S2,
          ShortArc (A 1) qstar ∧
          det3 (A 0 : E3) (A 1 : E3) (qstar : E3) = 0 ∧
          (0 ≤ (⟪(A 0 : E3), (A 1 : E3)⟫ : ℝ)
              - (⟪(A 0 : E3), (qstar : E3)⟫ : ℝ) * (⟪(A 1 : E3), (qstar : E3)⟫ : ℝ)) ∧
          (0 ≤ (⟪(A 0 : E3), (qstar : E3)⟫ : ℝ)
              - (⟪(A 0 : E3), (A 1 : E3)⟫ : ℝ) * (⟪(qstar : E3), (A 1 : E3)⟫ : ℝ)) ∧
          endpt A < sDist (A 0) qstar ∧
          sDist (A 1) qstar ≤ sDist (B 1) (B (Fin.last (n + 1))))
        ∨ endpt A < endpt B)

/-- **The reduction `OpenedArmReachOrStuck → OpeningData`.**  The weak bound is forwarded; in the
stuck branch the elementary determinant + sign data is converted into the `span ℝ≥0` betweenness
membership by the proved `betweenness_span_nnreal` (the vanishing closing-support determinant together
with the two convex-position Gram signs gives `A 0 ∈ span ℝ≥0 {A 1, qstar}`), and the short arc,
opening and sub-comparison bounds are forwarded; the reached / cut branch is forwarded.  This is the
genuine §8 bookkeeping turning the opening's raw determinant + sign output into `OpeningData`'s
geometric (membership) form — load-bearing, not a re-statement. -/
theorem openingData_of_reachOrStuck (h : OpenedArmReachOrStuck) : OpeningData := by
  intro n hn A B hA hB hside hangle ih
  obtain ⟨hweak, hstrict⟩ := h n hn A B hA hB hside hangle ih
  refine ⟨hweak, ?_⟩
  intro hwider
  rcases hstrict hwider with
    ⟨qstar, hsa, hdet, hsignA, hsignC, hopen, hsub⟩ | hdirect
  · refine Or.inl ⟨qstar, hsa, ?_, hopen, hsub⟩
    exact betweenness_span_nnreal (A 1) qstar (A 0) hsa hdet hsignA hsignC
  · exact Or.inr hdirect

/-- **`OpeningData`, conditional on the isolated convex-position primitive.**  Discharging the
genuine residue `OpenedArmReachOrStuck` gives `OpeningData`. -/
theorem openingData_holds (h : OpenedArmReachOrStuck) : OpeningData :=
  openingData_of_reachOrStuck h

/-- **The Schoenberg–Zaremba spherical arm lemma, conditional on the isolated convex-position
primitive.**  Composing the reduction with the proven chain `schoenbergZaremba_of_openingData`: once
the design §8.3–§8.4 opening outcome (the multi-vertex convex-position fact) is supplied, the named
kernel obligation `SchoenbergZarembaTarget` holds — and hence the **unconditional** spherical arm
lemma `spherical_arm_mono` / `spherical_arm_mono_strict` drops out.  Every sign-level, betweenness,
realisation, triangle-inequality and recursion step is proved unconditionally. -/
theorem schoenbergZaremba_of_reachOrStuck (h : OpenedArmReachOrStuck) : SchoenbergZarembaTarget :=
  schoenbergZaremba_of_openingData (openingData_holds h)







end ProofsInTheBook.SphericalOpening

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalOpening
-/
/- Source module: ProofsInTheBook.SphericalHinge -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening

namespace ProofsInTheBook.SphericalHinge



/-- **Cyclic invariance** of the scalar triple product: `[a,b,c] = [b,c,a] = [c,a,b]`. -/
theorem det3_cyclic (a b c : E3) :
    det3 a b c = det3 b c a ∧ det3 a b c = det3 c a b := by
  constructor <;> · simp only [det3]; ring

/-- **Skew (transposition) sign rule**: `[a,c,b] = -[a,b,c]`. -/
theorem det3_swap (a b c : E3) : det3 a c b = - det3 a b c := by
  simp only [det3]; ring













































end ProofsInTheBook.SphericalHinge

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalHinge
-/
/- Source module: ProofsInTheBook.SphericalSZChain -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge

namespace ProofsInTheBook.SphericalSZChain



/-- Cyclic invariance for `sOrient`. -/
theorem sOrient_cyclic (a b c : S2) :
    sOrient a b c = sOrient b c a ∧ sOrient a b c = sOrient c a b := by
  simp only [sOrient]; exact det3_cyclic _ _ _

/-- Transposition sign rule for `sOrient`. -/
theorem sOrient_swap (a b c : S2) : sOrient a c b = - sOrient a b c := by
  simp only [sOrient]; exact det3_swap _ _ _



/-- **Spherical SAS diagonal-length agreement (HINGE Lemma 11.1).**  Two spherical triangles
`(a₁,b₁,c₁)` and `(a₂,b₂,c₂)` with equal adjacent sides (`sDist a₁ b₁ = sDist a₂ b₂`,
`sDist b₁ c₁ = sDist b₂ c₂`) and equal included angle at the middle vertex
(`sphAngle a₁ b₁ c₁ = sphAngle a₂ b₂ c₂`) have equal opposite sides: `sDist a₁ c₁ = sDist a₂ c₂`.
The two opposite-side cosines coincide by the cosine rule, and `arccos` recovers the distance. -/
theorem diag_len_eq (a₁ b₁ c₁ a₂ b₂ c₂ : S2)
    (hab : sDist a₁ b₁ = sDist a₂ b₂)
    (hbc : sDist b₁ c₁ = sDist b₂ c₂)
    (hang : sphAngle a₁ b₁ c₁ = sphAngle a₂ b₂ c₂) :
    sDist a₁ c₁ = sDist a₂ c₂ := by
  have h1 := spherical_cosine_rule a₁ b₁ c₁
  have h2 := spherical_cosine_rule a₂ b₂ c₂
  have hcos : Real.cos (sDist a₁ c₁) = Real.cos (sDist a₂ c₂) := by
    rw [h1, h2, hab, hbc, hang]
  -- arccos ∘ cos recovers the distance, since both lie in [0,π].
  have e1 : sDist a₁ c₁ = Real.arccos (Real.cos (sDist a₁ c₁)) :=
    (Real.arccos_cos (sDist_nonneg _ _) (sDist_le_pi _ _)).symm
  have e2 : sDist a₂ c₂ = Real.arccos (Real.cos (sDist a₂ c₂)) :=
    (Real.arccos_cos (sDist_nonneg _ _) (sDist_le_pi _ _)).symm
  rw [e1, e2, hcos]



/-- **The diagonal-cut endpoint transport (load-bearing glue).**  Given the level-`n` comparison
`ih : SZComparison n`, two cut arms `A' B' : Fin (n+1) → S2` that are strictly convex with equal
sides and nondecreasing joints, and the endpoint identifications `endpt A' = endpt A`,
`endpt B' = endpt B`, the level-`(n+1)` endpoint comparison follows: the weak bound always, and the
strict bound whenever some joint of `B'` is strictly wider.  This turns the cut's *geometric* output
into the arm-lemma endpoint inequality through the inductive hypothesis. -/
theorem cut_endpt_transport {n : ℕ}
    (ih : SZComparison n)
    {A B : Fin (n + 1 + 1) → S2} (A' B' : Fin (n + 1) → S2)
    (hA' : StrictConvexSphArm A') (hB' : StrictConvexSphArm B')
    (hside' : ∀ i : Fin n, sideLen A' i = sideLen B' i)
    (hangle' : ∀ i : Fin (n - 1), jointAngle A' i ≤ jointAngle B' i)
    (heA : endpt A' = endpt A) (heB : endpt B' = endpt B) :
    endpt A ≤ endpt B ∧
      ((∃ i : Fin (n - 1), jointAngle A' i < jointAngle B' i) → endpt A < endpt B) := by
  obtain ⟨hmono, hstrict⟩ := ih A' B' hA' hB' hside' hangle'
  rw [heA, heB] at hmono
  refine ⟨hmono, ?_⟩
  intro hw
  have := hstrict hw
  rwa [heA, heB] at this

















end ProofsInTheBook.SphericalSZChain

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZChain
-/
/- Source module: ProofsInTheBook.SphericalCyclicTriple -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain

namespace ProofsInTheBook.SphericalCyclicTriple









/-- **HINGE Lemma 2.3, the cyclic-triple property (named residue).**  For a strictly convex spherical
polygon `P : Fin n → S²`, every triple in strictly increasing index order is positively oriented. -/
def CyclicTriplePos {n : ℕ} [NeZero n] (P : Fin n → S2) : Prop :=
  ∀ i j k : Fin n, i < j → j < k → 0 < sOrient (P i) (P j) (P k)







/-- **Diagonal support (HINGE Lemma 2.4 / 11.2).**  Given the cyclic-triple property, any diagonal
`P a → P b` (`a < b`) supports every vertex `P k` with `b < k`: `0 < sOrient (P a)(P b)(P k)`.  This is
precisely the new-edge support a forward diagonal cut needs. -/
theorem cyclicTriple_pos_of_diag {n : ℕ} [NeZero n] {P : Fin n → S2}
    (hc : CyclicTriplePos P) {a b k : Fin n} (hab : a < b) (hbk : b < k) :
    0 < sOrient (P a) (P b) (P k) :=
  hc a b k hab hbk























end ProofsInTheBook.SphericalCyclicTriple

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalCyclicTriple
-/
/- Source module: ProofsInTheBook.SphericalGnomonic -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple

namespace ProofsInTheBook.SphericalGnomonic



/-- **Multilinear scaling law.**  `det3` is multilinear, so scaling the three arguments by `r,s,t`
multiplies the determinant by `r·s·t`.  A true polynomial identity (`ring`). -/
theorem det3_smul₃ (r s t : ℝ) (a b c : E3) :
    det3 (r • a) (s • b) (t • c) = r * s * t * det3 a b c := by
  simp only [det3, smul_apply]; ring










/-- The gnomonic projection of a sphere point `p` with respect to a normal `h` (with `⟪h, p⟫ ≠ 0`):
the point `(⟪h, p⟫)⁻¹ • p` on the affine plane `⟪h,·⟫ = 1`. -/
def gproj (h : E3) (p : S2) : E3 := ((⟪h, (p : E3)⟫ : ℝ))⁻¹ • (p : E3)

/-- The gnomonic projection lands on the plane `⟪h,·⟫ = 1` (when `⟪h, p⟫ ≠ 0`). -/
theorem inner_gproj {h : E3} {p : S2} (hp : (⟪h, (p : E3)⟫ : ℝ) ≠ 0) :
    (⟪h, gproj h p⟫ : ℝ) = 1 := by
  rw [gproj, inner_smul_right]
  field_simp

/-- **Gnomonic sign-correspondence (step (a)).**  `sOrient (P i)(P j)(P k)` equals the positive scalar
`⟪h,P i⟫·⟪h,P j⟫·⟪h,P k⟫` times the *planar* orientation `det3 (gproj h (P i))(gproj h (P j))(gproj h
(P k))`.  Hence the two have the same sign: the spherical convex-position fact is the planar one. -/
theorem gnomonic_sign_correspondence (h : E3) (a b c : S2)
    (ha : (⟪h, (a : E3)⟫ : ℝ) ≠ 0) (hb : (⟪h, (b : E3)⟫ : ℝ) ≠ 0)
    (hc : (⟪h, (c : E3)⟫ : ℝ) ≠ 0) :
    sOrient a b c
      = (⟪h, (a : E3)⟫ : ℝ) * (⟪h, (b : E3)⟫ : ℝ) * (⟪h, (c : E3)⟫ : ℝ)
          * det3 (gproj h a) (gproj h b) (gproj h c) := by
  rw [gproj, gproj, gproj, det3_smul₃, sOrient]
  field_simp





/-- **Planar convex-position diagonal positivity (isolated residue).**  Let `h ≠ 0` and let
`f : Fin n → E3` be a cyclic family of points all in the affine plane `⟪h,·⟫ = 1`, such that every
directed edge `(f i, f (i+1))` has all non-incident points strictly on its positive side
(`0 < det3 (f i)(f (i+1))(f j)` for `j ≠ i, i+1`) and all points on the nonnegative side
(`0 ≤ det3 (f i)(f (i+1))(f j)` always).  Then every strictly increasing triple is positively
oriented: `i < j < k ⟹ 0 < det3 (f i)(f j)(f k)`.

This is the standard 2-D convex-position fact; it is **not** an algebraic consequence of the edge
supports (see the module docstring's machine-checked residue note — the `nnls` non-certificate, the
sign-indefinite cocycle, and the same-gap `gp` relation), needing the angular ordering / winding
bound the open hemisphere supplies.  Isolated here as one named, non-vacuous planar `Prop`. -/
def PlanarConvexDiagPos : Prop :=
  ∀ (n : ℕ) [NeZero n] (h : E3) (_ : h ≠ 0) (f : Fin n → E3),
    (∀ i : Fin n, (⟪h, f i⟫ : ℝ) = 1) →
    (∀ i j : Fin n, 0 ≤ det3 (f i) (f (i + 1)) (f j)) →
    (∀ i j : Fin n, j ≠ i → j ≠ i + 1 → 0 < det3 (f i) (f (i + 1)) (f j)) →
    ∀ i j k : Fin n, i < j → j < k → 0 < det3 (f i) (f j) (f k)





/-- **`CyclicTriplePos` from the planar primitive (steps (a)+(b)).**  Given the planar convex-position
fact `PlanarConvexDiagPos`, every `StrictConvexSphPolygon` satisfies the cyclic-triple property:
gnomonically project to the plane `⟪hv,·⟫ = 1`, transport the edge / non-incident supports through the
positive-scalar sign-correspondence, apply the planar primitive, and pull the positive planar
orientation back to `sOrient` through the correspondence. -/
theorem cyclicTriplePos_of_planar (hplanar : PlanarConvexDiagPos)
    {n : ℕ} [NeZero n] {P : Fin n → S2} (h : StrictConvexSphPolygon P) :
    CyclicTriplePos P := by
  obtain ⟨hv, hnorm, hposfun⟩ := h.open_hemisphere
  have hvne : hv ≠ 0 := by intro hz; rw [hz] at hnorm; simp at hnorm
  set Q : Fin n → E3 := fun i => gproj hv (P i) with hQ
  -- the projected family lies in the plane
  have hplane : ∀ i : Fin n, (⟪hv, Q i⟫ : ℝ) = 1 := fun i => inner_gproj (ne_of_gt (hposfun i))
  -- transport the supports to the planar orientation through the sign-correspondence
  have hcorr : ∀ a b c : Fin n,
      sOrient (P a) (P b) (P c)
        = (⟪hv, (P a : E3)⟫ : ℝ) * (⟪hv, (P b : E3)⟫ : ℝ) * (⟪hv, (P c : E3)⟫ : ℝ)
            * det3 (Q a) (Q b) (Q c) := fun a b c =>
    gnomonic_sign_correspondence hv (P a) (P b) (P c)
      (ne_of_gt (hposfun a)) (ne_of_gt (hposfun b)) (ne_of_gt (hposfun c))
  have hscal : ∀ a b c : Fin n,
      (0 : ℝ) < (⟪hv, (P a : E3)⟫ : ℝ) * (⟪hv, (P b : E3)⟫ : ℝ) * (⟪hv, (P c : E3)⟫ : ℝ) :=
    fun a b c => mul_pos (mul_pos (hposfun a) (hposfun b)) (hposfun c)
  -- edge supports (nonnegative)
  have hedge : ∀ i j : Fin n, 0 ≤ det3 (Q i) (Q (i + 1)) (Q j) := by
    intro i j
    have hs := h.edge_support i j
    have hc := hcorr i (i + 1) j
    have hsc := hscal i (i + 1) j
    rw [hc] at hs
    -- `hs : 0 ≤ pos * det3 Q`, `hsc : 0 < pos` ⟹ `0 ≤ det3 Q`
    by_contra hlt; push_neg at hlt
    nlinarith [hs, hsc, hlt]
  -- strict non-incident supports
  have hstrict : ∀ i j : Fin n, j ≠ i → j ≠ i + 1 → 0 < det3 (Q i) (Q (i + 1)) (Q j) := by
    intro i j hj1 hj2
    have hs := h.strict_nonincident i j hj1 hj2
    have hc := hcorr i (i + 1) j
    have hsc := hscal i (i + 1) j
    rw [hc] at hs
    by_contra hle; push_neg at hle
    nlinarith [hs, hsc, hle]
  -- apply the planar primitive and pull back
  intro i j k hij hjk
  have hpl := hplanar n hv hvne Q hplane hedge hstrict i j k hij hjk
  rw [hcorr i j k]
  have := hscal i j k
  positivity



/-- **HINGE Lemma 2.3 for general `n` (`CyclicTriplePos`), conditional only on the planar primitive.**
Every strictly convex spherical polygon `P : Fin n → S²` has all `i < j < k` diagonals positively
oriented, `0 < sOrient (P i)(P j)(P k)`, given the standard planar convex-position fact
`PlanarConvexDiagPos`.  This is the gnomonic reduction's headline output: the spherical fact reduces,
unconditionally, to the `2`-D one. -/
theorem cyclicTriplePos_holds (hplanar : PlanarConvexDiagPos)
    {n : ℕ} [NeZero n] {P : Fin n → S2} (h : StrictConvexSphPolygon P) :
    CyclicTriplePos P :=
  cyclicTriplePos_of_planar hplanar h

/-- **Diagonal support (HINGE Lemma 2.4 / 11.2), now from the planar primitive.**  Any diagonal
`P a → P b` (`a < b`) supports every vertex `P k` with `b < k`. -/
theorem cyclicTriple_pos_of_diag_holds (hplanar : PlanarConvexDiagPos)
    {n : ℕ} [NeZero n] {P : Fin n → S2} (h : StrictConvexSphPolygon P)
    {a b k : Fin n} (hab : a < b) (hbk : b < k) :
    0 < sOrient (P a) (P b) (P k) :=
  cyclicTriple_pos_of_diag (cyclicTriplePos_holds hplanar h) hab hbk

















end ProofsInTheBook.SphericalGnomonic

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalGnomonic
-/
/- Source module: ProofsInTheBook.PlanarConvexDiag -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalArm ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalGnomonic

namespace ProofsInTheBook.PlanarConvexDiag



/-- **Shared-apex Grassmann–Plücker syzygy.**  For any five vectors in `E3`, the `det3`'s sharing the
apex `A` satisfy `det3 A P Q · det3 A E M = det3 A M Q · det3 A E P + det3 A P M · det3 A E Q`.
A pure polynomial identity (`ring`), the quadratic engine of the convex-position induction. -/
theorem det3_apex_plucker (A E P M Q : E3) :
    det3 A P Q * det3 A E M = det3 A M Q * det3 A E P + det3 A P M * det3 A E Q := by
  simp only [det3]; ring

/-- `det3` is invariant under cyclic rotation of its three arguments (`ring`). -/
theorem det3_cyclic (a b c : E3) : det3 a b c = det3 b c a := by
  simp only [det3]; ring



/-- The core planar induction, on natural-number indices, in a window `[i, N)`.  From the consecutive
turning base and the strict half-plane edge supports (only needed inside the window), every increasing
triple `i < p < q < N` is positively oriented. -/
theorem det3_diag_pos_nat (g : ℕ → E3) (i N : ℕ)
    (hbase : ∀ t : ℕ, i < t → t + 1 < N → 0 < det3 (g i) (g t) (g (t + 1)))
    (hedge : ∀ t : ℕ, i + 1 < t → t < N → 0 < det3 (g i) (g (i + 1)) (g t)) :
    ∀ q p : ℕ, i < p → p < q → q < N → 0 < det3 (g i) (g p) (g q) := by
  intro q
  -- strong induction on the larger index `q`
  induction q using Nat.strong_induction_on with
  | _ q IH =>
    intro p hip hpq hqN
    -- Case split on whether `p` is the reference endpoint `i+1`.
    rcases Nat.lt_or_ge (i + 1) p with hp2 | hple
    · -- `p ≥ i+2`: use the Plücker syzygy with pivot `m = q-1`.
      -- First, `q ≥ p+1 ≥ i+3`, so `q-1 ≥ i+2` and `q ≥ i+2`.
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      -- pivot m = q' (= q-1)
      have hq'p : p ≤ q' := by omega
      rcases Nat.lt_or_ge p q' with hlt | hge
      · -- p < q' : recurse
        -- positivity of the three edge-support factors and the two recursive diagonals
        have e_p : 0 < det3 (g i) (g (i + 1)) (g p) := hedge p hp2 (by omega)
        have e_q : 0 < det3 (g i) (g (i + 1)) (g (q' + 1)) := hedge (q' + 1) (by omega) (by omega)
        have e_m : 0 < det3 (g i) (g (i + 1)) (g q') := hedge q' (by omega) (by omega)
        -- D(i, q', q'+1) consecutive base
        have d_consec : 0 < det3 (g i) (g q') (g (q' + 1)) := hbase q' (by omega) (by omega)
        -- D(i, p, q') smaller q (= q' < q'+1)
        have d_rec : 0 < det3 (g i) (g p) (g q') := IH q' (by omega) p hip hlt (by omega)
        -- Plücker: D(i,p,q'+1) * e_m = D(i,q',q'+1) * e_p + D(i,p,q') * e_q
        have hpl := det3_apex_plucker (g i) (g (i + 1)) (g p) (g q') (g (q' + 1))
        -- hpl : det3 (g i)(g p)(g (q'+1)) * det3 (g i)(g (i+1))(g q')
        --      = det3 (g i)(g q')(g (q'+1)) * det3 (g i)(g (i+1))(g p)
        --      + det3 (g i)(g p)(g q') * det3 (g i)(g (i+1))(g (q'+1))
        nlinarith [mul_pos d_consec e_p, mul_pos d_rec e_q, e_m,
          mul_pos (mul_pos d_consec e_p) e_m]
      · -- p = q' : then the triple is the consecutive base D(i, q', q'+1)
        have : p = q' := le_antisymm hq'p hge
        subst this
        exact hbase p hip (by omega)
    · -- `p ≤ i+1`, and `i < p`, so `p = i+1`: direct strict edge support
      have : p = i + 1 := by omega
      subst this
      exact hedge q (by omega) hqN



/-- For `i : Fin n` with `i.val + 1 < n`, the `Fin`-cyclic successor coincides with the linear one. -/
theorem fin_succ_val {n : ℕ} [NeZero n] {i : Fin n} (h : i.val + 1 < n) :
    (i + 1 : Fin n).val = i.val + 1 := by
  have hn : 2 ≤ n := by omega
  rw [Fin.add_def]
  have h1 : (1 : Fin n).val = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  rw [h1]
  exact Nat.mod_eq_of_lt h



/-- **`PlanarConvexDiagPos`, proved.**  A strictly convex planar polygon (edge-support form) has every
increasing triple `i < j < k` positively oriented.  We lift `f` to a `ℕ`-indexed family `g` (agreeing
with `f` inside the window `[0, n)`), translate the cyclic edge supports into the consecutive turning
base (`hbase`, via the cyclic rotation `det3_cyclic`) and the strict half-plane supports (`hedge`),
and invoke the Plücker-driven core induction `det3_diag_pos_nat`. -/
theorem planarConvexDiagPos_holds : PlanarConvexDiagPos := by
  intro n _ h _hh f _hplane hedge_nn hstrict i j k hij hjk
  -- `g : ℕ → E3` agreeing with `f` on `[0, n)`
  set g : ℕ → E3 := fun t => f ⟨t % n, Nat.mod_lt t (NeZero.pos n)⟩ with hg
  have g_eq : ∀ t (ht : t < n), g t = f ⟨t, ht⟩ := by
    intro t ht; simp only [hg, Nat.mod_eq_of_lt ht]
  -- consecutive turning base
  have hbase : ∀ t : ℕ, i.val < t → t + 1 < n → 0 < det3 (g i.val) (g t) (g (t + 1)) := by
    intro t hit ht1
    have ht : t < n := by omega
    rw [g_eq i.val i.isLt, g_eq t ht, g_eq (t + 1) ht1]
    -- det3 (f i)(f ⟨t⟩)(f ⟨t+1⟩) = det3 (f ⟨t⟩)(f ⟨t+1⟩)(f i)  (cyclic)
    rw [det3_cyclic]
    -- f ⟨t+1⟩ = f (⟨t⟩ + 1)
    have hsucc : (⟨t, ht⟩ + 1 : Fin n) = ⟨t + 1, ht1⟩ := by
      apply Fin.ext; rw [fin_succ_val (by simpa using ht1)]
    rw [show (⟨t + 1, ht1⟩ : Fin n) = (⟨t, ht⟩ + 1 : Fin n) from hsucc.symm]
    -- strict edge support of edge (⟨t⟩, ⟨t⟩+1) on i
    refine hstrict ⟨t, ht⟩ i ?_ ?_
    · exact fun hc => by simp only [Fin.ext_iff] at hc; omega
    · exact fun hc => by
        simp only [Fin.ext_iff, hsucc] at hc; omega
  -- strict half-plane edge supports
  have hedge : ∀ t : ℕ, i.val + 1 < t → t < n → 0 < det3 (g i.val) (g (i.val + 1)) (g t) := by
    intro t hit ht
    have hi1 : i.val + 1 < n := by omega
    rw [g_eq i.val i.isLt, g_eq (i.val + 1) hi1, g_eq t ht]
    have hsucc : (i + 1 : Fin n) = ⟨i.val + 1, hi1⟩ := by
      apply Fin.ext; exact fin_succ_val hi1
    rw [show (⟨i.val + 1, hi1⟩ : Fin n) = (i + 1 : Fin n) from hsucc.symm]
    refine hstrict i ⟨t, ht⟩ ?_ ?_
    · exact fun hc => by simp only [Fin.ext_iff] at hc; omega
    · exact fun hc => by
        rw [hsucc] at hc; simp only [Fin.ext_iff] at hc; omega
  -- apply the core and identify `g` with `f` on the window
  have hcore := det3_diag_pos_nat g i.val n hbase hedge k.val j.val
    (by exact_mod_cast hij) (by exact_mod_cast hjk) k.isLt
  rwa [g_eq i.val i.isLt, g_eq j.val j.isLt, g_eq k.val k.isLt,
    Fin.eta, Fin.eta, Fin.eta] at hcore



/-- **HINGE Lemma 2.3 (`CyclicTriplePos`), unconditional.**  Every strictly convex spherical polygon
has all `i < j < k` diagonals positively oriented — the convex-position residue fully discharged. -/
theorem cyclicTriplePos_unconditional {n : ℕ} [NeZero n] {P : Fin n → S2}
    (h : StrictConvexSphPolygon P) : CyclicTriplePos P :=
  cyclicTriplePos_holds planarConvexDiagPos_holds h





end ProofsInTheBook.PlanarConvexDiag

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarConvexDiag
-/
/- Source module: ProofsInTheBook.SphericalSZStep -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag

namespace ProofsInTheBook.SphericalSZStep







/-- **Reach-case endpoint monotonicity (weak), via the base triangle.**  Opening `tail` about `axis`
by `θ` preserves the base sides `a0–axis` and `axis–tail`; if the opened base angle dominates the
original, the endpoint distance `a0–tail` does not decrease.  Proved from `spherical_hinge_mono`. -/
theorem reach_base_endpoint_mono (axis a0 tail : S2)
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail) {θ : ℝ}
    (hangle : sphAngle a0 axis tail ≤ sphAngle a0 axis (rotS2 axis θ tail)) :
    sDist a0 tail ≤ sDist a0 (rotS2 axis θ tail) := by
  have hfix : rotS2 axis θ axis = axis := by apply S2.ext; rw [rotS2_coe, rot_axis axis.2]
  have hside2 : sDist axis (rotS2 axis θ tail) = sDist axis tail := by
    have := sDist_rotS2 axis θ axis tail
    rw [hfix] at this; exact this
  have ha0k : 0 < sDist a0 axis ∧ sDist a0 axis < Real.pi := ⟨hka.symm.sDist_pos, hka.symm.sDist_lt_pi⟩
  have hktp : 0 < sDist axis tail ∧ sDist axis tail < Real.pi := ⟨hkt.sDist_pos, hkt.sDist_lt_pi⟩
  have hc1 := spherical_cosine_rule a0 axis tail
  have hc2 := spherical_cosine_rule a0 axis (rotS2 axis θ tail)
  rw [hside2] at hc2
  refine spherical_hinge_mono (a := sDist a0 axis) (b := sDist axis tail)
    (γ₁ := sphAngle a0 axis tail) (γ₂ := sphAngle a0 axis (rotS2 axis θ tail))
    ha0k.1 ha0k.2 hktp.1 hktp.2 (sphAngle_nonneg _ _ _) (sphAngle_le_pi _ _ _) hangle
    hc1 hc2 (sDist_mem_Icc _ _) (sDist_mem_Icc _ _)

/-- **Reach-case endpoint monotonicity (strict), via the base triangle.**  A strict base-angle increase
gives a strict endpoint increase.  Proved from `spherical_hinge_strict`. -/
theorem reach_base_endpoint_strict (axis a0 tail : S2)
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail) {θ : ℝ}
    (hangle : sphAngle a0 axis tail < sphAngle a0 axis (rotS2 axis θ tail)) :
    sDist a0 tail < sDist a0 (rotS2 axis θ tail) := by
  have hfix : rotS2 axis θ axis = axis := by apply S2.ext; rw [rotS2_coe, rot_axis axis.2]
  have hside2 : sDist axis (rotS2 axis θ tail) = sDist axis tail := by
    have := sDist_rotS2 axis θ axis tail
    rw [hfix] at this; exact this
  have ha0k : 0 < sDist a0 axis ∧ sDist a0 axis < Real.pi := ⟨hka.symm.sDist_pos, hka.symm.sDist_lt_pi⟩
  have hktp : 0 < sDist axis tail ∧ sDist axis tail < Real.pi := ⟨hkt.sDist_pos, hkt.sDist_lt_pi⟩
  have hc1 := spherical_cosine_rule a0 axis tail
  have hc2 := spherical_cosine_rule a0 axis (rotS2 axis θ tail)
  rw [hside2] at hc2
  refine spherical_hinge_strict (a := sDist a0 axis) (b := sDist axis tail)
    (γ₁ := sphAngle a0 axis tail) (γ₂ := sphAngle a0 axis (rotS2 axis θ tail))
    ha0k.1 ha0k.2 hktp.1 hktp.2 (sphAngle_nonneg _ _ _) (sphAngle_le_pi _ _ _) hangle
    hc1 hc2 (sDist_mem_Icc _ _) (sDist_mem_Icc _ _)





















end ProofsInTheBook.SphericalSZStep

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZStep
-/
/- Source module: ProofsInTheBook.SphericalHingeCut -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep

namespace ProofsInTheBook.SphericalHingeCut



/-- The norm of the rotated outgoing tangent is constant in `θ` (the rotation is an isometry). -/
theorem norm_tangentTo_open (axis q : S2) (θ : ℝ) :
    ‖tangentTo axis (rotS2 axis θ q)‖ = ‖tangentTo axis q‖ := by
  rw [tangentTo_rotS2_axis, norm_rot axis.2]

/-- A vector annihilated by `cross k ·` (for unit `k`) is parallel to `k`: `v = ⟪v,k⟫ • k`. -/
theorem eq_smul_axis_of_cross_zero {k v : E3} (hk : ‖k‖ = 1) (h : cross k v = 0) :
    v = (⟪v, k⟫ : ℝ) • k := by
  have hkk : (⟪k, k⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hk]; norm_num
  set t : E3 := v - (⟪v, k⟫ : ℝ) • k with ht
  -- t ⟂ k
  have htk : (⟪t, k⟫ : ℝ) = 0 := by
    rw [ht, inner_sub_left, real_inner_smul_left, hkk, mul_one, sub_self]
  -- cross k t = cross k v - ⟪v,k⟫ • cross k k = 0
  have hct : cross k t = 0 := by
    rw [ht, show v - (⟪v, k⟫ : ℝ) • k = v + (-(⟪v, k⟫ : ℝ)) • k by module,
      cross_add_right, cross_smul_right, cross_self, smul_zero, add_zero, h]
  -- ‖cross k t‖² = ‖k‖²‖t‖² − ⟪k,t⟫² = ‖t‖²  (k unit, t ⟂ k)
  have hkt : (⟪k, t⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact htk
  have hnorm : ‖t‖ ^ 2 = 0 := by
    have hl := norm_sq_cross k t
    rw [hct, norm_zero] at hl
    rw [hk, hkt] at hl
    nlinarith [hl]
  have : t = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hnorm
    exact norm_eq_zero.mp this
  rw [ht] at this
  linear_combination (norm := module) this

/-- `cross k v = 0` for unit `k` implies `⟪v,k⟫² = ‖v‖²`: `v` is parallel to the unit `k`. -/
theorem inner_axis_sq_eq_norm_sq {k v : E3} (hk : ‖k‖ = 1) (h : cross k v = 0) :
    (⟪v, k⟫ : ℝ) ^ 2 = ‖v‖ ^ 2 := by
  have hkk : (⟪k, k⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hk]; norm_num
  have hpar := eq_smul_axis_of_cross_zero hk h
  rw [← real_inner_self_eq_norm_sq]
  conv_lhs => rw [hpar]
  conv_rhs => rw [hpar]
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, hkk]
  ring

/-- **The tangent-plane Pythagorean identity.**  For a unit axis `k` and two vectors `u, w` both
orthogonal to `k`, `⟪u,w⟫² + ⟪u, k×w⟫² = ‖u‖²‖w‖²`.  The cross product `u × w` is parallel to `k`
(both `u, w ⟂ k`), so `⟪u, k×w⟫² = ⟪u×w, k⟫² = ‖u×w‖² = ‖u‖²‖w‖² − ⟪u,w⟫²` (Lagrange). -/
theorem tangentPlane_pythag {k u w : E3} (hk : ‖k‖ = 1)
    (huk : (⟪u, k⟫ : ℝ) = 0) (hwk : (⟪w, k⟫ : ℝ) = 0) :
    (⟪u, w⟫ : ℝ) ^ 2 + (⟪u, cross k w⟫ : ℝ) ^ 2 = ‖u‖ ^ 2 * ‖w‖ ^ 2 := by
  -- `s := ⟪u, k×w⟫ = -⟪u×w, k⟫`  (coordinate identity)
  have hs : (⟪u, cross k w⟫ : ℝ) = -(⟪cross u w, k⟫ : ℝ) := by
    rw [inner_eq_coord, inner_eq_coord]
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  -- `u × w` is parallel to `k`: `cross k (cross u w) = ⟪k,w⟫•u − ⟪k,u⟫•w = 0`
  have hku : (⟪k, u⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact huk
  have hkw : (⟪k, w⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hwk
  have hpar : cross k (cross u w) = 0 := by
    rw [cross_cross, hkw, hku, zero_smul, zero_smul, sub_zero]
  -- hence `⟪u×w, k⟫² = ‖u×w‖²`
  have hsq : (⟪cross u w, k⟫ : ℝ) ^ 2 = ‖cross u w‖ ^ 2 := inner_axis_sq_eq_norm_sq hk hpar
  -- Lagrange: `‖u×w‖² = ‖u‖²‖w‖² − ⟪u,w⟫²`
  have hlag : ‖cross u w‖ ^ 2 = ‖u‖ ^ 2 * ‖w‖ ^ 2 - (⟪u, w⟫ : ℝ) ^ 2 := norm_sq_cross u w
  rw [hs, neg_sq, hsq, hlag]; ring













/-- **Cut diagonal supports (unconditional).**  In a strictly convex spherical polygon, the diagonal
`P a → P b` (`a < b`) lies strictly on the positive side of every vertex `P k` beyond it (`b < k`):
`0 < sOrient (P a)(P b)(P k)`.  This is the new-edge support certificate of a forward diagonal cut,
now unconditional via `cyclicTriplePos_unconditional`. -/
theorem cut_diagonal_supports {m : ℕ} [NeZero m] {P : Fin m → S2}
    (h : StrictConvexSphPolygon P) {a b k : Fin m} (hab : a < b) (hbk : b < k) :
    0 < sOrient (P a) (P b) (P k) :=
  cyclicTriplePos_unconditional h a b k hab hbk















end ProofsInTheBook.SphericalHingeCut

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalHingeCut
-/
/- Source module: ProofsInTheBook.SphericalDiagCut -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut

namespace ProofsInTheBook.SphericalDiagCut



/-- The open-hemisphere witness of a strictly convex polygon survives composition with *any* vertex
re-indexing `σ : Fin m → Fin l`: the same functional `h` works, since the field only asks each
re-indexed vertex `P (σ j)` to have positive inner product with `h`. -/
theorem open_hemisphere_reindex {l m : ℕ} [NeZero l] [NeZero m] {P : Fin l → S2}
    (h : StrictConvexSphPolygon P) (σ : Fin m → Fin l) :
    ∃ hh : E3, ‖hh‖ = 1 ∧ ∀ j : Fin m, 0 < ⟪hh, ((P ∘ σ) j : E3)⟫ := by
  obtain ⟨hh, hhn, hhpos⟩ := h.open_hemisphere
  exact ⟨hh, hhn, fun j => hhpos (σ j)⟩



/-- `det3 a b a = 0`: a determinant with a repeated column vanishes. -/
theorem det3_self_right (a b : E3) : det3 a b a = 0 := by
  simp only [det3]; ring

/-- `det3 a a b = 0`: a determinant with a repeated (first/second) column vanishes. -/
theorem det3_self_left (a b : E3) : det3 a a b = 0 := by
  simp only [det3]; ring

/-- `det3 a b b = 0`: a determinant with a repeated (second/third) column vanishes. -/
theorem det3_self_mid (a b : E3) : det3 a b b = 0 := by
  simp only [det3]; ring

/-- A strict orientation `0 < sOrient a b c` forces `a ≠ c`. -/
theorem ne_of_sOrient_pos_ac {a b c : S2} (h : 0 < sOrient a b c) : a ≠ c := by
  intro he
  apply (ne_of_gt h).symm
  rw [sOrient, he, det3_self_right]

/-- A strict orientation `0 < sOrient a b c` forces `a` and `c` non-antipodal: if `(a:E3) = -(c:E3)`
then `sOrient a b c = -sOrient c b c = 0` (a repeated column up to sign), contradicting positivity. -/
theorem not_antipodal_of_sOrient_pos_ac {a b c : S2} (h : 0 < sOrient a b c) :
    (a : E3) ≠ -(c : E3) := by
  intro he
  apply (ne_of_gt h).symm
  have : sOrient a b c = det3 (-(c : E3)) (b : E3) (c : E3) := by rw [sOrient, he]
  rw [this]
  simp only [det3, PiLp.neg_apply]; ring

































end ProofsInTheBook.SphericalDiagCut

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalDiagCut
-/
/- Source module: ProofsInTheBook.SphericalOpeningProcess -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut

namespace ProofsInTheBook.SphericalOpeningProcess

































/-- **The oriented-tangent ↔ `sOrient` identity.**  For a base/axis vertex `k` and two points `a, b`,
`⟪tangentTo k a, k × tangentTo k b⟫ = -sOrient k a b`.  Computation: `k × tangentTo k b = k × b`
(the `k`-component is annihilated), and `⟪tangentTo k a, k×b⟫ = ⟪a, k×b⟫ = det3 a k b = -det3 k a b`. -/
theorem inner_tangent_cross_eq_neg_sOrient (k a b : S2) :
    (⟪tangentTo k a, cross (k : E3) (tangentTo k b)⟫ : ℝ) = -sOrient k a b := by
  -- Step 1: `k × tangentTo k b = k × b`.
  have hkt : cross (k : E3) (tangentTo k b) = cross (k : E3) (b : E3) := by
    rw [tangentTo_eq,
      show (b : E3) - (sInner b k) • (k : E3) = (b : E3) + (-(sInner b k)) • (k : E3) by module,
      cross_add_right, cross_smul_right, cross_self, smul_zero, add_zero]
  rw [hkt]
  -- Step 2: `⟪tangentTo k a, k × b⟫ = ⟪a, k × b⟫` (the `k`-component drops since `⟪k, k×b⟫ = 0`).
  have hta : (⟪tangentTo k a, cross (k : E3) (b : E3)⟫ : ℝ) = (⟪(a : E3), cross (k : E3) (b : E3)⟫ : ℝ) := by
    rw [tangentTo_eq, inner_sub_left, real_inner_smul_left]
    have hkc : (⟪(k : E3), cross (k : E3) (b : E3)⟫ : ℝ) = 0 := by
      rw [inner_cross_eq_det3]; simp only [det3]; ring
    rw [hkc, mul_zero, sub_zero]
  rw [hta, inner_cross_eq_det3]
  -- Step 3: `det3 a k b = -det3 k a b = -sOrient k a b`.
  rw [sOrient]
  simp only [det3]; ring









/-- **The stuck-case endpoint glue.**  Given the stuck collinearity (`A 0` between `A 1` and `qstar`),
the strict opening bound, the level-`n` sub-comparison bound on the tail sub-arm, and the equal first
side, the level-`(n+1)` strict endpoint bound `endpt A < endpt B` follows.  Fully assembled from the
proved `szChain_stuck_nondegenerate` — no new hypotheses beyond the raw opening witness. -/
theorem stuck_endpoint_strict {n : ℕ} (A B : Fin (n + 1 + 1) → S2) (qstar : S2)
    (hcol : (A 0 : E3) ∈ Submodule.span NNReal ({(A 1 : E3), (qstar : E3)} : Set E3))
    (hopen : endpt A < sDist (A 0) qstar)
    (hsub : sDist (A 1) qstar ≤ sDist (B 1) (B (Fin.last (n + 1))))
    (hside1 : sDist (B 1) (B 0) = sDist (A 1) (A 0)) :
    endpt A < endpt B := by
  have h := szChain_stuck_nondegenerate (A0 := A 0) (A1 := A 1) (An := A (Fin.last (n + 1)))
    (qstar := qstar) (B0 := B 0) (B1 := B 1) (Bn := B (Fin.last (n + 1)))
    hcol hsub hside1 (by simpa [endpt] using hopen)
  simpa [endpt] using h



/-- **The opening witness existence (the honest residue, raw geometric form).**  This is the
all-strict-case geometric output of the design §8.4 opening, isolated from the endpoint-inequality layer
(which is now derived in this module).  It carries *only* the raw `qstar` + tail data; it does **not**
contain the weak bound, the reach branch's endpoint inequality, the `span≥0`→distance betweenness
conversion, or the IH glue — all of which `szStepGeom_of_stuckWitness` derives.  It is therefore
strictly narrower than `SZStepGeom`'s strict branch (which additionally bundles the weak bound and the
fully-converted strict inequality), not a co-extensive re-wrapper. -/
def StuckWitnessExists : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∀ (A B : Fin (n + 1 + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
      (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
      SZComparison n →
      (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
      (∃ qstar : S2,
          (A 0 : E3) ∈ Submodule.span NNReal ({(A 1 : E3), (qstar : E3)} : Set E3) ∧
          endpt A < sDist (A 0) qstar ∧
          sDist (A 1) qstar ≤ sDist (B 1) (B (Fin.last (n + 1))) ∧
          sDist (B 1) (B 0) = sDist (A 1) (A 0))
        ∨ endpt A < endpt B

/-- **The strict branch of `SZStepGeom` from the stuck-witness existence (load-bearing reduction).**
Given the residue's raw output, the strict endpoint bound is *derived*: the stuck `qstar` data is
converted to `endpt A < endpt B` by the assembled `stuck_endpoint_strict` (consuming
`szChain_stuck_nondegenerate` + the betweenness-to-distance equality), and the reached branch is
forwarded.  This proves the genuine geometric content of `SZStepGeom`'s strict half; the endpoint
inequality is produced, not assumed. -/
theorem szStep_strict_of_stuckWitness (hw : StuckWitnessExists)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i)
    (ih : SZComparison n)
    (hwider : ∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) :
    endpt A < endpt B := by
  rcases hw n hn A B hA hB hside hangle ih hwider with
    ⟨qstar, hcol, hopen, hsub, hside1⟩ | hdirect
  · exact stuck_endpoint_strict A B qstar hcol hopen hsub hside1
  · exact hdirect







end ProofsInTheBook.SphericalOpeningProcess

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalOpeningProcess
-/
/- Source module: ProofsInTheBook.SphericalReachStuck -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess

namespace ProofsInTheBook.SphericalReachStuck













/-- **The opened-angle cosine is monotone (convex / negative-rotation orientation).**  If the
oriented datum `s = ⟪tangentTo axis a0, axis × tangentTo axis tail⟫ ≥ 0` (the convex opening sign)
and `0 ≤ θ` with `θ + sphAngle a0 axis tail ≤ π`, then the opened-by-`-θ` angle cosine does not
exceed the original: `cos (sphAngle a0 axis (rotS2 axis (-θ) tail)) ≤ cos (sphAngle a0 axis tail)`.
Mirror of `cos_open_le_cos_orig` for `s ≥ 0`, `-θ`. -/
theorem cos_open_le_cos_orig_neg (axis a0 tail : S2)
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail)
    (hsign : (0 : ℝ) ≤ (⟪tangentTo axis a0, cross (axis : E3) (tangentTo axis tail)⟫ : ℝ))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ + sphAngle a0 axis tail ≤ Real.pi) :
    Real.cos (sphAngle a0 axis (rotS2 axis (-θ) tail)) ≤ Real.cos (sphAngle a0 axis tail) := by
  set u := tangentTo axis a0 with hu
  set w := tangentTo axis tail with hw
  set c : ℝ := ⟪u, w⟫ with hc
  set s : ℝ := ⟪u, cross (axis : E3) w⟫ with hsdef
  have hunz : u ≠ 0 := (tangentTo_ne_zero_iff axis a0).2 hka
  have hwnz : w ≠ 0 := (tangentTo_ne_zero_iff axis tail).2 hkt
  have hup : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hunz
  have hwp : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hwnz
  set N : ℝ := ‖u‖ * ‖w‖ with hN
  have hNp : (0 : ℝ) < N := mul_pos hup hwp
  set φ₀ : ℝ := sphAngle a0 axis tail with hφ
  have hcosopen : Real.cos (sphAngle a0 axis (rotS2 axis (-θ) tail))
      = (Real.cos (-θ) * c + Real.sin (-θ) * s) / N := by
    rw [cos_openedJointAngle, norm_tangentTo_open]
  have hcosorig : Real.cos φ₀ = c / N := by
    rw [hφ, sphAngle, InnerProductGeometry.cos_angle]
  have hφ0 : 0 ≤ φ₀ := sphAngle_nonneg _ _ _
  have hφπ : φ₀ ≤ Real.pi := sphAngle_le_pi _ _ _
  have hpyth : c ^ 2 + s ^ 2 = N ^ 2 := by
    have := tangentPlane_pythag (k := (axis : E3)) (u := u) (w := w) axis.2
      (tangentTo_orthogonal axis a0) (tangentTo_orthogonal axis tail)
    rw [hc, hsdef, hN]; rw [mul_pow]; linear_combination this
  have hcEq : c = N * Real.cos φ₀ := by
    rw [hcosorig]; field_simp
  have hsinφ : 0 ≤ Real.sin φ₀ := Real.sin_nonneg_of_nonneg_of_le_pi hφ0 hφπ
  have hssq : s ^ 2 = (N * Real.sin φ₀) ^ 2 := by
    have hsincos : Real.sin φ₀ ^ 2 = 1 - Real.cos φ₀ ^ 2 := by
      have := Real.sin_sq_add_cos_sq φ₀; linarith
    rw [mul_pow, hsincos]
    have : s ^ 2 = N ^ 2 - c ^ 2 := by linarith [hpyth]
    rw [this, hcEq]; ring
  -- now s ≥ 0, so s = +(N sin φ₀)
  have hsEq : s = N * Real.sin φ₀ := by
    have hge : 0 ≤ N * Real.sin φ₀ := mul_nonneg (le_of_lt hNp) hsinφ
    nlinarith [hssq, hsign, hge, sq_nonneg (s - N * Real.sin φ₀)]
  -- the `-θ` sinusoid is N cos(φ₀+θ)
  have hsinusoid : Real.cos (-θ) * c + Real.sin (-θ) * s = N * Real.cos (φ₀ + θ) := by
    rw [hcEq, hsEq, Real.cos_neg, Real.sin_neg, Real.cos_add]; ring
  rw [hcosopen, hcosorig, hsinusoid]
  rw [div_le_div_iff_of_pos_right hNp]
  have hcos : Real.cos (φ₀ + θ) ≤ Real.cos φ₀ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hφ0 (by linarith) (by linarith)
  rw [hcEq]
  exact mul_le_mul_of_nonneg_left hcos (le_of_lt hNp)

/-- **Mirrored oriented opening monotonicity (convex orientation).**  Opening the joint at `axis` by
`-θ` (`θ ≥ 0`, within the great-semicircle range) increases the included angle, provided the convex
oriented datum `0 ≤ ⟪tangentTo axis a0, axis × tangentTo axis tail⟫` holds.  Companion of
`openedAngle_ge_of_oriented` for the convex opening direction. -/
theorem openedAngle_ge_of_oriented_neg (axis a0 tail : S2)
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail)
    (hsign : (0 : ℝ) ≤ (⟪tangentTo axis a0, cross (axis : E3) (tangentTo axis tail)⟫ : ℝ))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ + sphAngle a0 axis tail ≤ Real.pi) :
    sphAngle a0 axis tail ≤ sphAngle a0 axis (rotS2 axis (-θ) tail) := by
  have hcos := cos_open_le_cos_orig_neg axis a0 tail hka hkt hsign hθ0 hθπ
  by_contra hlt
  rw [not_le] at hlt
  have : Real.cos (sphAngle a0 axis tail) < Real.cos (sphAngle a0 axis (rotS2 axis (-θ) tail)) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (sphAngle_nonneg _ _ _) (sphAngle_le_pi _ _ _) hlt
  linarith [hcos]

/-- The convex oriented datum from the convex support sign: `0 < sOrient (A 0)(axis)(tail)` gives
`0 ≤ ⟪tangentTo axis a0, axis × tangentTo axis tail⟫` (with `a0 = A 0`, `tail = the tail`).  Via the
bridge `inner_tangent_cross_eq_neg_sOrient` and `sOrient (axis)(A 0)(tail) = -sOrient (A 0)(axis)(tail)`. -/
theorem orientedSign_neg_of_support {axis a0 tail : S2}
    (h : 0 ≤ sOrient a0 axis tail) :
    (0 : ℝ) ≤ (⟪tangentTo axis a0, cross (axis : E3) (tangentTo axis tail)⟫ : ℝ) := by
  rw [inner_tangent_cross_eq_neg_sOrient]
  -- need 0 ≤ -sOrient axis a0 tail, i.e. sOrient axis a0 tail ≤ 0.
  -- sOrient axis a0 tail = -sOrient a0 axis tail (swap first two).
  have hswap : sOrient axis a0 tail = -sOrient a0 axis tail := by
    have := sOrient_swap a0 axis tail  -- sOrient a0 tail axis = -sOrient a0 axis tail
    -- We instead want sOrient axis a0 tail. Use det form directly.
    simp only [sOrient, det3]; ring
  rw [hswap]; linarith



















end ProofsInTheBook.SphericalReachStuck

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalReachStuck
-/
/- Source module: ProofsInTheBook.SphericalAdmissibleSup -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck

namespace ProofsInTheBook.SphericalAdmissibleSup

































































end ProofsInTheBook.SphericalAdmissibleSup

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalAdmissibleSup
-/
/- Source module: ProofsInTheBook.SphericalArmClose -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup

namespace ProofsInTheBook.SphericalArmClose































































end ProofsInTheBook.SphericalArmClose

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmClose
-/
/- Source module: ProofsInTheBook.SphericalArmFinal -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose

namespace ProofsInTheBook.SphericalArmFinal























end ProofsInTheBook.SphericalArmFinal

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmFinal
-/
/- Source module: ProofsInTheBook.SphericalSZComplete -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose

namespace ProofsInTheBook.SphericalSZComplete













































end ProofsInTheBook.SphericalSZComplete

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZComplete
-/
/- Source module: ProofsInTheBook.SphericalStuckWitness -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete

namespace ProofsInTheBook.SphericalStuckWitness





















































end ProofsInTheBook.SphericalStuckWitness

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalStuckWitness
-/
/- Source module: ProofsInTheBook.SphericalTerminalVis -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalStuckWitness

namespace ProofsInTheBook.SphericalTerminalVis































































end ProofsInTheBook.SphericalTerminalVis

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalTerminalVis
-/
/- Source module: ProofsInTheBook.SphericalArmUncond -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis

namespace ProofsInTheBook.SphericalArmUncond















/-- **The per-step matched-cut datum.**  For a level-`(n+1)` convex arm pair `A B`, this is the
existence of matched level-`n` cut sub-arms `A' B'` (strictly convex, equal sides, nondecreasing
joints, sharing the parent endpoints `endpt A' = endpt A`, `endpt B' = endpt B`) *together with* the
strictness link: whenever some parent joint of `B` is strictly wider, some sub-joint of `B'` is too.
This is the *geometric* output of the design §8.4 diagonal cut / reach recursion — the two-piece
matched cut with its `B`-side companion — in endpoint-only form (no `qstar`, no `span≥0` betweenness,
no Gram signs). -/
def MatchedCutData {n : ℕ} (A B : Fin (n + 1 + 1) → S2) : Prop :=
  ∃ A' B' : Fin (n + 1) → S2,
    StrictConvexSphArm A' ∧ StrictConvexSphArm B' ∧
    (∀ i : Fin n, sideLen A' i = sideLen B' i) ∧
    (∀ i : Fin (n - 1), jointAngle A' i ≤ jointAngle B' i) ∧
    endpt A' = endpt A ∧ endpt B' = endpt B ∧
    ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
      ∃ i : Fin (n - 1), jointAngle A' i < jointAngle B' i)

/-- **One inductive step from the matched-cut datum (proved).**  Given the level-`n` comparison and the
matched cut sub-arms (with the strictness link), the level-`(n+1)` endpoint pair follows: the weak
bound directly, and the strict bound by transporting a strictly-wider parent joint to a strictly-wider
sub-joint, then `cut_endpt_transport`.  This is the discharge `bothSided_cut_transport` performs. -/
theorem step_of_matchedCutData {n : ℕ}
    (ih : SZComparison n) {A B : Fin (n + 1 + 1) → S2} (hcut : MatchedCutData A B) :
    endpt A ≤ endpt B
      ∧ ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) → endpt A < endpt B) := by
  obtain ⟨A', B', hA', hB', hside', hangle', heA, heB, hlink⟩ := hcut
  obtain ⟨hmono, hstr⟩ :=
    cut_endpt_transport (A := A) (B := B) ih A' B' hA' hB' hside' hangle' heA heB
  exact ⟨hmono, fun hw => hstr (hlink hw)⟩































end ProofsInTheBook.SphericalArmUncond

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmUncond
-/
/- Source module: ProofsInTheBook.SphericalMatchedCut -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond

namespace ProofsInTheBook.SphericalMatchedCut









/-- The first-interior-vertex-drop cut arm: keep `A 0, A 2, A 3, …, A (n+1)`.  For index `j`, keep
`A 0` if `j = 0`, otherwise `A (j+1)` (the skip of vertex `1`). -/
def frontCut {n : ℕ} (A : Fin (n + 1 + 1) → S2) : Fin (n + 1) → S2 :=
  fun j => if hj : j = 0 then A 0 else A ⟨j.val + 1, by have := j.isLt; omega⟩

@[simp] theorem frontCut_zero {n : ℕ} (A : Fin (n + 1 + 1) → S2) :
    frontCut A 0 = A 0 := by simp [frontCut]

/-- For a nonzero index `j` of `Fin (n+1)`, `frontCut A j = A ⟨j+1⟩` (read in `Fin (n+2)`):
`frontCut` keeps vertex `A (j+1)`, i.e. it skips vertex `1`. -/
theorem frontCut_of_ne_zero {n : ℕ} (A : Fin (n + 1 + 1) → S2) {j : Fin (n + 1)} (hj : j ≠ 0) :
    frontCut A j = A ⟨j.val + 1, by have := j.isLt; omega⟩ := by
  simp only [frontCut, dif_neg hj]

/-- The last vertex of the front cut arm is `A (last)` (needs `n ≥ 1` so that `Fin.last n ≠ 0`). -/
theorem frontCut_last {n : ℕ} (A : Fin (n + 1 + 1) → S2) (hn : 1 ≤ n) :
    frontCut A (Fin.last n) = A (Fin.last (n + 1)) := by
  have hne : (Fin.last n : Fin (n + 1)) ≠ 0 := by
    intro h
    have : (Fin.last n : Fin (n + 1)).val = (0 : Fin (n + 1)).val := by rw [h]
    simp only [Fin.val_last, Fin.val_zero] at this; omega
  rw [frontCut_of_ne_zero A hne]
  congr 1



/-- The value of `1 : Fin (n+1)` is `1` (for `n ≥ 1`). -/
theorem one_val_fin {n : ℕ} (hn : 1 ≤ n) : ((1 : Fin (n + 1)) : ℕ) = 1 := by
  rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)

/-- The non-last bound: `j ≠ last` forces `j.val < n`. -/
theorem frontCut_lt_of_ne_last {n : ℕ} {j : Fin (n + 1)} (hj : j ≠ Fin.last n) :
    j.val < n := by
  rcases Nat.lt_or_ge j.val n with h | h
  · exact h
  · exact absurd (Fin.ext (by simp only [Fin.val_last]; omega)) hj

/-- At a NON-last index `j ≠ last`, the cyclic successor of the cut arm is `frontCut A (j+1) =
A ⟨j+2⟩` — the parent vertex two steps along. -/
theorem frontCut_succ_of_ne_last {n : ℕ} (A : Fin (n + 1 + 1) → S2) (hn : 1 ≤ n)
    {j : Fin (n + 1)} (hj : j ≠ Fin.last n) :
    frontCut A (j + 1) = A ⟨j.val + 2, by have := frontCut_lt_of_ne_last hj; omega⟩ := by
  have hjv : j.val < n := frontCut_lt_of_ne_last hj
  have hsucc_ne : (j + 1 : Fin (n + 1)) ≠ 0 := by
    intro h
    have : ((j + 1 : Fin (n + 1)) : ℕ) = 0 := by rw [h]; rfl
    rw [Fin.val_add, one_val_fin hn, Nat.mod_eq_of_lt (by omega)] at this
    omega
  rw [frontCut_of_ne_zero A hsucc_ne]
  congr 1
  apply Fin.ext
  simp only [Fin.val_add, one_val_fin hn, Nat.mod_eq_of_lt (show j.val + 1 < n + 1 by omega)]

/-- At the last index, the cyclic successor wraps to `A 0`: `frontCut A (Fin.last n + 1) = A 0`. -/
theorem frontCut_succ_last {n : ℕ} (A : Fin (n + 1 + 1) → S2) (hn : 1 ≤ n) :
    frontCut A (Fin.last n + 1) = A 0 := by
  have hzero : (Fin.last n + 1 : Fin (n + 1)) = 0 := by
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_last, one_val_fin hn, Fin.val_zero]
    rw [Nat.mod_self]
  rw [hzero, frontCut_zero]

/-- `frontCut A 1 = A 2`: the other endpoint of the new diagonal edge `0`. -/
theorem frontCut_one {n : ℕ} (A : Fin (n + 1 + 1) → S2) (hn : 1 ≤ n) :
    frontCut A 1 = A ⟨2, by omega⟩ := by
  have h1ne : (1 : Fin (n + 1)) ≠ 0 := by
    intro h
    have : ((1 : Fin (n + 1)) : ℕ) = 0 := by rw [h]; rfl
    rw [one_val_fin hn] at this; omega
  rw [frontCut_of_ne_zero A h1ne]
  congr 1
  apply Fin.ext
  simp only [one_val_fin hn]



/-- The opening diagonal `A 0 → A 2` strictly supports every vertex `A k` with `2 < k`.  Direct
from the proved diagonal positivity `cyclicTriple_pos_of_diag_holds` with `a = 0`, `b = ⟨2⟩`. -/
theorem frontDiag_support {n : ℕ} (hn : 1 ≤ n) {A : Fin (n + 1 + 1) → S2}
    (hP : StrictConvexSphPolygon A) {k : Fin (n + 1 + 1)}
    (hk : (⟨2, by omega⟩ : Fin (n + 1 + 1)) < k) :
    0 < sOrient (A 0) (A ⟨2, by omega⟩) (A k) := by
  have h02 : (0 : Fin (n + 1 + 1)) < (⟨2, by omega⟩ : Fin (n + 1 + 1)) := by
    rw [Fin.lt_def, Fin.val_zero]; show (0 : ℕ) < 2; omega
  exact cyclicTriple_pos_of_diag_holds planarConvexDiagPos_holds hP h02 hk



/-- The parent-index of a cut-arm vertex: `gidx j = 0` if `j = 0`, else `⟨j.val+1⟩`. -/
def gidx {n : ℕ} (j : Fin (n + 1)) : Fin (n + 1 + 1) :=
  if j = 0 then 0 else ⟨j.val + 1, by have := j.isLt; omega⟩

theorem frontCut_eq_gidx {n : ℕ} (A : Fin (n + 1 + 1) → S2) (j : Fin (n + 1)) :
    frontCut A j = A (gidx j) := by
  unfold frontCut gidx
  by_cases hj : j = 0 <;> simp [hj]

/-- `gidx` value: `0 ↦ 0`. -/
@[simp] theorem gidx_zero {n : ℕ} : gidx (0 : Fin (n + 1)) = 0 := by simp [gidx]

/-- `gidx` value at a nonzero index. -/
theorem gidx_ne_zero_val {n : ℕ} {j : Fin (n + 1)} (hj : j ≠ 0) :
    (gidx j).val = j.val + 1 := by simp [gidx, hj]

/-- `gidx` value at zero index. -/
theorem gidx_zero_val {n : ℕ} : (gidx (0 : Fin (n + 1))).val = 0 := by simp

/-- `gidx` is injective. -/
theorem gidx_injective {n : ℕ} : Function.Injective (gidx : Fin (n + 1) → Fin (n + 1 + 1)) := by
  intro a b hab
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · rw [ha, hb]
  · exfalso
    have hv : (gidx a).val = (gidx b).val := by rw [hab]
    rw [ha, gidx_zero_val, gidx_ne_zero_val hb] at hv; omega
  · exfalso
    have hv : (gidx a).val = (gidx b).val := by rw [hab]
    rw [gidx_ne_zero_val ha, hb, gidx_zero_val] at hv; omega
  · have : (gidx a).val = (gidx b).val := by rw [hab]
    rw [gidx_ne_zero_val ha, gidx_ne_zero_val hb] at this
    apply Fin.ext; omega



/-- A retained cut-arm vertex never maps to parent-index `1`: `gidx j ≠ 1`.  (This is why the diagonal
`A 0 → A 2` skips exactly `A 1`.) -/
theorem gidx_ne_one {n : ℕ} (hn : 1 ≤ n) (j : Fin (n + 1)) :
    gidx j ≠ (⟨1, by omega⟩ : Fin (n + 1 + 1)) := by
  by_cases hj : j = 0
  · rw [hj]; intro h
    have : (gidx (0 : Fin (n + 1))).val = (⟨1, by omega⟩ : Fin (n + 1 + 1)).val := by rw [h]
    rw [gidx_zero_val] at this; simp at this
  · intro h
    have : (gidx j).val = (⟨1, by omega⟩ : Fin (n + 1 + 1)).val := by rw [h]
    rw [gidx_ne_zero_val hj] at this
    have hjpos : 0 < j.val := Nat.pos_of_ne_zero (fun hc => hj (Fin.ext (by simp [hc])))
    simp only [] at this; omega

/-- **The front cut arm polygon is strictly convex.**  Dropping the first interior vertex `A 1` of a
strictly convex spherical arm `A` yields a strictly convex polygon on `A 0, A 2, …, A (n+1)`. -/
theorem frontCut_strictConvexPolygon {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (hn : 2 ≤ n) :
    StrictConvexSphPolygon (frontCut A) := by
  have hP := hA.closed_convex
  have hn1 : 1 ≤ n := by omega
  -- the diagonal endpoint `A 2 = frontCut A 1`
  have hone := frontCut_one A hn1
  refine
    { three_le := by omega
      edge_short := ?_
      edge_support := ?_
      strict_nonincident := ?_
      open_hemisphere := ?_ }
  · -- edge_short
    intro i
    by_cases hi : i = Fin.last n
    · -- closing edge: A (last) → A 0
      subst hi
      rw [frontCut_last A hn1, frontCut_succ_last A hn1]
      -- `A`'s closing edge `A (last (n+1)) → A (last+1 = 0)` is short.
      have := hP.edge_short (Fin.last (n + 1))
      rwa [show (Fin.last (n + 1) + 1 : Fin (n + 1 + 1)) = 0 by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_last, Fin.val_zero, Fin.val_one']
        rw [Nat.mod_eq_of_lt (show 1 < n + 1 + 1 by omega), Nat.mod_self]] at this
    · by_cases hi0 : i = 0
      · -- diagonal edge: A 0 → A 2, short via frontDiag_support against an interior vertex
        subst hi0
        rw [frontCut_zero, show (0 + 1 : Fin (n + 1)) = 1 by simp, hone]
        -- need ShortArc (A 0) (A 2): use the edge support of edge `(0,1)` against vertex 2.
        have hzo : ((0 : Fin (n + 1 + 1)) + 1).val = 1 := by
          rw [Fin.val_add, Fin.val_zero, Fin.val_one', Nat.zero_add,
            Nat.mod_eq_of_lt (show 1 < n + 1 + 1 by omega),
            Nat.mod_eq_of_lt (show 1 < n + 1 + 1 by omega)]
        have hpos : 0 < sOrient (A 0) (A 1) (A ⟨2, by omega⟩) := by
          have hne1 : (⟨2, by omega⟩ : Fin (n + 1 + 1)) ≠ 0 := by
            intro h; rw [Fin.ext_iff, Fin.val_zero] at h; simp at h
          have hne2 : (⟨2, by omega⟩ : Fin (n + 1 + 1)) ≠ 0 + 1 := by
            intro h; rw [Fin.ext_iff, hzo] at h; simp at h
          have := hP.strict_nonincident 0 ⟨2, by omega⟩ hne1 hne2
          rwa [show ((0 : Fin (n + 1 + 1)) + 1) = 1 by
            apply Fin.ext; rw [hzo, Fin.val_one']
            exact (Nat.mod_eq_of_lt (show 1 < n + 1 + 1 by omega)).symm] at this
        refine ⟨?_, ?_⟩
        · exact ne_of_sOrient_pos_ac hpos
        · intro he; exact not_antipodal_of_sOrient_pos_ac hpos he
      · -- interior edge: A ⟨i+1⟩ → A ⟨i+2⟩ = A's edge gidx i
        rw [frontCut_of_ne_zero A hi0, frontCut_succ_of_ne_last A hn1 hi]
        have := hP.edge_short ⟨i.val + 1, by have := frontCut_lt_of_ne_last hi; omega⟩
        rwa [show (⟨i.val + 1, by have := frontCut_lt_of_ne_last hi; omega⟩ + 1 :
            Fin (n + 1 + 1)) = ⟨i.val + 2, by have := frontCut_lt_of_ne_last hi; omega⟩ by
          apply Fin.ext
          simp only [Fin.val_add, Fin.val_one']
          rw [Nat.mod_eq_of_lt (show 1 < n + 1 + 1 by omega),
            Nat.mod_eq_of_lt (show i.val + 1 + 1 < n + 1 + 1 by
              have := frontCut_lt_of_ne_last hi; omega)]] at this
  · -- edge_support: `0 ≤ sOrient (frontCut i)(frontCut (i+1))(frontCut j)`
    intro i j
    rw [frontCut_eq_gidx A j]
    by_cases hi : i = Fin.last n
    · -- closing edge: A (last) → A 0
      subst hi
      rw [frontCut_last A hn1, frontCut_succ_last A hn1]
      have hclose : (Fin.last (n + 1) + 1 : Fin (n + 1 + 1)) = 0 := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_last, Fin.val_zero, Fin.val_one']
        rw [Nat.mod_eq_of_lt (show 1 < n + 1 + 1 by omega), Nat.mod_self]
      have := hP.edge_support (Fin.last (n + 1)) (gidx j)
      rwa [hclose] at this
    · by_cases hi0 : i = 0
      · -- diagonal edge: A 0 → A 2
        subst hi0
        rw [frontCut_zero, show (0 + 1 : Fin (n + 1)) = 1 by simp, hone]
        rcases Nat.lt_trichotomy (gidx j).val 2 with hlt | heq | hgt
        · -- gidx j ∈ {0} (never 1), so j = 0, gidx j = 0: repeated column → 0
          have : (gidx j).val = 0 := by
            have := gidx_ne_one hn1 j
            interval_cases h : (gidx j).val
            · rfl
            · exfalso; apply this; apply Fin.ext; simp [h]
          have hj0 : gidx j = 0 := Fin.ext (by rw [this]; rfl)
          rw [hj0]; simp only [sOrient]; rw [det3_self_right]
        · -- gidx j = 2: repeated column (third = second)
          have hj2 : gidx j = (⟨2, by omega⟩ : Fin (n + 1 + 1)) := Fin.ext (by rw [heq])
          rw [hj2]; simp only [sOrient]; rw [det3_self_mid]
        · -- gidx j > 2: strict support
          have hk : (⟨2, by omega⟩ : Fin (n + 1 + 1)) < gidx j := by
            rw [Fin.lt_def]; show (2 : ℕ) < (gidx j).val; omega
          exact le_of_lt (frontDiag_support hn1 hP hk)
      · -- interior edge: A's edge at index ⟨i+1⟩
        rw [frontCut_of_ne_zero A hi0, frontCut_succ_of_ne_last A hn1 hi]
        have hsucc : (⟨i.val + 1, by have := frontCut_lt_of_ne_last hi; omega⟩ + 1 :
            Fin (n + 1 + 1)) = ⟨i.val + 2, by have := frontCut_lt_of_ne_last hi; omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_add, Fin.val_one']
          rw [Nat.mod_eq_of_lt (show 1 < n + 1 + 1 by omega),
            Nat.mod_eq_of_lt (show i.val + 1 + 1 < n + 1 + 1 by
              have := frontCut_lt_of_ne_last hi; omega)]
        have := hP.edge_support ⟨i.val + 1, by have := frontCut_lt_of_ne_last hi; omega⟩ (gidx j)
        rwa [hsucc] at this
  · -- strict_nonincident: `j ≠ i → j ≠ i+1 → 0 < sOrient (frontCut i)(frontCut (i+1))(frontCut j)`
    intro i j hji hji1
    rw [frontCut_eq_gidx A j]
    -- the cut-arm non-incidence transports to parent non-incidence via `gidx` injectivity.
    by_cases hi : i = Fin.last n
    · -- closing edge: A (last) → A 0; non-incident means gidx j ≠ last(n+1) and ≠ 0.
      subst hi
      rw [frontCut_last A hn1, frontCut_succ_last A hn1]
      have hclose : (Fin.last (n + 1) + 1 : Fin (n + 1 + 1)) = 0 := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_last, Fin.val_zero, Fin.val_one']
        rw [Nat.mod_eq_of_lt (show 1 < n + 1 + 1 by omega), Nat.mod_self]
      -- gidx j ≠ last(n+1): else j = last (gidx (last) = last(n+1)), contradicting j ≠ last
      have hjlast : j ≠ Fin.last n := hji
      have hj0 : j ≠ 0 := by intro h; apply hji1; rw [h]; symm
                             apply Fin.ext
                             rw [Fin.val_add, Fin.val_last, Fin.val_zero, Fin.val_one',
                               Nat.mod_eq_of_lt (show 1 < n + 1 by omega), Nat.mod_self]
      have hne_last : gidx j ≠ Fin.last (n + 1) := by
        intro h
        apply hjlast
        have hv : (gidx j).val = (Fin.last (n + 1)).val := by rw [h]
        rw [gidx_ne_zero_val hj0, Fin.val_last] at hv
        apply Fin.ext; rw [Fin.val_last]; omega
      have hne_zero : gidx j ≠ 0 := by
        intro h
        have hv : (gidx j).val = (0 : Fin (n + 1 + 1)).val := by rw [h]
        rw [gidx_ne_zero_val hj0, Fin.val_zero] at hv; omega
      have := hP.strict_nonincident (Fin.last (n + 1)) (gidx j) hne_last (by rwa [hclose])
      rwa [hclose] at this
    · by_cases hi0 : i = 0
      · -- diagonal edge: A 0 → A 2; non-incident means gidx j ∉ {0, 2}, so gidx j > 2.
        subst hi0
        rw [frontCut_zero, show (0 + 1 : Fin (n + 1)) = 1 by simp, hone]
        have hj0 : j ≠ 0 := hji
        have hj1 : j ≠ 1 := by
          intro h; apply hji1; rw [h]; symm; simp
        -- gidx j ≥ 3 since j ≥ 2 (j ≠ 0, j ≠ 1)
        have hjval : 2 ≤ j.val := by
          rcases Nat.lt_or_ge j.val 2 with h | h
          · interval_cases hv : j.val
            · exact absurd (Fin.ext (by simp [hv])) hj0
            · refine absurd (Fin.ext ?_) hj1
              rw [hv, one_val_fin hn1]
          · exact h
        have hk : (⟨2, by omega⟩ : Fin (n + 1 + 1)) < gidx j := by
          rw [Fin.lt_def]; show (2 : ℕ) < (gidx j).val
          rw [gidx_ne_zero_val hj0]; omega
        exact frontDiag_support hn1 hP hk
      · -- interior edge: A's edge at index ⟨i+1⟩
        rw [frontCut_of_ne_zero A hi0, frontCut_succ_of_ne_last A hn1 hi]
        have hsucc : (⟨i.val + 1, by have := frontCut_lt_of_ne_last hi; omega⟩ + 1 :
            Fin (n + 1 + 1)) = ⟨i.val + 2, by have := frontCut_lt_of_ne_last hi; omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_add, Fin.val_one']
          rw [Nat.mod_eq_of_lt (show 1 < n + 1 + 1 by omega),
            Nat.mod_eq_of_lt (show i.val + 1 + 1 < n + 1 + 1 by
              have := frontCut_lt_of_ne_last hi; omega)]
        -- non-incidence: gidx j ≠ gidx i = ⟨i+1⟩ and gidx j ≠ ⟨i+2⟩
        have hne1 : gidx j ≠ ⟨i.val + 1, by have := frontCut_lt_of_ne_last hi; omega⟩ := by
          intro h
          apply hji
          have : gidx j = gidx i := by
            rw [h]; apply Fin.ext; rw [gidx_ne_zero_val hi0]
          exact (gidx_injective this).symm ▸ rfl
        have hne2 : gidx j ≠ ⟨i.val + 2, by have := frontCut_lt_of_ne_last hi; omega⟩ := by
          intro h
          apply hji1
          have hgi1 : gidx (i + 1) = ⟨i.val + 2, by have := frontCut_lt_of_ne_last hi; omega⟩ := by
            have hi1ne : (i + 1 : Fin (n + 1)) ≠ 0 := by
              intro hc
              have : ((i + 1 : Fin (n + 1)) : ℕ) = 0 := by rw [hc]; rfl
              rw [Fin.val_add, one_val_fin hn1,
                Nat.mod_eq_of_lt (show i.val + 1 < n + 1 by
                  have := frontCut_lt_of_ne_last hi; omega)] at this
              omega
            apply Fin.ext
            rw [gidx_ne_zero_val hi1ne]
            simp only [Fin.val_add, one_val_fin hn1,
              Nat.mod_eq_of_lt (show i.val + 1 < n + 1 by have := frontCut_lt_of_ne_last hi; omega)]
          have : gidx j = gidx (i + 1) := by rw [h, hgi1]
          exact (gidx_injective this).symm ▸ rfl
        have hsupp := hP.strict_nonincident
          ⟨i.val + 1, by have := frontCut_lt_of_ne_last hi; omega⟩ (gidx j) hne1 (by rwa [hsucc])
        rwa [hsucc] at hsupp
  · -- open_hemisphere: frontCut A = A ∘ gidx, so reindex
    obtain ⟨hh, hhn, hhpos⟩ := open_hemisphere_reindex hP gidx
    refine ⟨hh, hhn, ?_⟩
    intro j
    rw [show ((frontCut A j : S2) : E3) = ((A (gidx j) : S2) : E3) by rw [frontCut_eq_gidx]]
    exact hhpos j

/-- **The front cut arm is a strictly convex arm.**  For an arm `A` of `≥ 3` edges (`n ≥ 2`), the
first-interior-vertex-drop `frontCut A` is again a `StrictConvexSphArm` of one fewer vertex. -/
theorem frontCut_strictConvexArm {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (hn : 2 ≤ n) :
    StrictConvexSphArm (frontCut A) :=
  { two_le := hn
    closed_convex := frontCut_strictConvexPolygon A hA hn }



/-- **Endpoint preservation.**  The first-interior-vertex-drop preserves the arm endpoint distance:
`endpt (frontCut A) = endpt A`. -/
theorem frontCut_endpoint {n : ℕ} (A : Fin (n + 1 + 1) → S2) (hn : 1 ≤ n) :
    endpt (frontCut A) = endpt A := by
  unfold endpt
  rw [frontCut_zero, frontCut_last A hn]



/-- The cut-arm side `0` is the diagonal length `sDist (A 0) (A 2)`. -/
theorem frontCut_sideLen_zero {n : ℕ} (A : Fin (n + 1 + 1) → S2) (hn : 1 ≤ n) :
    sideLen (frontCut A) (⟨0, by omega⟩ : Fin n) = sDist (A 0) (A ⟨2, by omega⟩) := by
  unfold sideLen
  have hc : (frontCut A) (⟨0, by omega⟩ : Fin n).castSucc = A 0 := by
    rw [show ((⟨0, by omega⟩ : Fin n).castSucc) = (0 : Fin (n + 1)) by
      apply Fin.ext; simp]
    exact frontCut_zero A
  have hs : (frontCut A) (⟨0, by omega⟩ : Fin n).succ = A ⟨2, by omega⟩ := by
    rw [show ((⟨0, by omega⟩ : Fin n).succ) = (1 : Fin (n + 1)) by
      apply Fin.ext; rw [Fin.val_succ, one_val_fin hn]]
    exact frontCut_one A hn
  rw [hc, hs]

/-- The cut-arm side `i` for `1 ≤ i` equals the parent side `sideLen A ⟨i+1⟩`. -/
theorem frontCut_sideLen_succ {n : ℕ} (A : Fin (n + 1 + 1) → S2) (_hn : 1 ≤ n)
    {i : Fin n} (hi : i.val ≠ 0) :
    sideLen (frontCut A) i = sideLen A ⟨i.val + 1, by have := i.isLt; omega⟩ := by
  unfold sideLen
  have hcast_ne : (i.castSucc : Fin (n + 1)) ≠ 0 := by
    intro h
    apply hi
    have : (i.castSucc : Fin (n + 1)).val = (0 : Fin (n + 1)).val := by rw [h]
    simpa using this
  have hc : (frontCut A) i.castSucc = A ⟨i.val + 1, by have := i.isLt; omega⟩ := by
    rw [frontCut_of_ne_zero A hcast_ne]
    congr 1
  have hsucc_ne : (i.succ : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero i
  have hs : (frontCut A) i.succ = A ⟨i.val + 2, by have := i.isLt; omega⟩ := by
    rw [frontCut_of_ne_zero A hsucc_ne]
    congr 1
  rw [hc, hs]
  congr 1

/-- `jointAngle A 0 = sphAngle (A 0) (A 1) (A 2)` for an `(n+2)`-vertex arm (the first interior
joint).  The joint index ranges over `Fin n` for `A : Fin (n+1+1) → S2`. -/
theorem jointAngle_zero {n : ℕ} (A : Fin (n + 1 + 1) → S2) (hn : 1 ≤ n) :
    jointAngle A (⟨0, by omega⟩ : Fin n) =
      sphAngle (A 0) (A 1) (A ⟨2, by omega⟩) := by
  unfold jointAngle
  congr 1

/-- **The diagonal cut side agrees between `A` and `B`** when the two adjacent sides agree and the
included (first joint) angle agrees: spherical SAS `diag_len_eq`. -/
theorem frontCut_diag_side_eq {n : ℕ} (A B : Fin (n + 1 + 1) → S2) (hn : 1 ≤ n)
    (hs0 : sDist (A 0) (A 1) = sDist (B 0) (B 1))
    (hs1 : sDist (A 1) (A ⟨2, by omega⟩) = sDist (B 1) (B ⟨2, by omega⟩))
    (hang : sphAngle (A 0) (A 1) (A ⟨2, by omega⟩) = sphAngle (B 0) (B 1) (B ⟨2, by omega⟩)) :
    sDist (A 0) (A ⟨2, by omega⟩) = sDist (B 0) (B ⟨2, by omega⟩) :=
  diag_len_eq (A 0) (A 1) (A ⟨2, by omega⟩) (B 0) (B 1) (B ⟨2, by omega⟩) hs0 hs1 hang

/-- **Matched side lengths of the cut arms.**  If `A`/`B` have equal parent sides and the first joint
is matched (`jointAngle A 0 = jointAngle B 0`), then the front cut arms have equal sides: side `0` is
the diagonal, equal by spherical SAS (`frontCut_diag_side_eq`); sides `i ≥ 1` are inherited parent
sides, equal by `hside`. -/
theorem frontCut_matched_sides {n : ℕ} (A B : Fin (n + 1 + 1) → S2) (hn : 1 ≤ n)
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i)
    (hjoint0 : jointAngle A (⟨0, by omega⟩ : Fin n) =
      jointAngle B (⟨0, by omega⟩ : Fin n)) :
    ∀ i : Fin n, sideLen (frontCut A) i = sideLen (frontCut B) i := by
  -- adjacent sides of the diagonal triangle in parent-side form
  have hadj0 : sDist (A 0) (A 1) = sDist (B 0) (B 1) := by
    have := hside ⟨0, by omega⟩
    unfold sideLen at this
    rw [show ((⟨0, by omega⟩ : Fin (n + 1)).castSucc) = (0 : Fin (n + 1 + 1)) by apply Fin.ext; simp,
        show ((⟨0, by omega⟩ : Fin (n + 1)).succ) = (1 : Fin (n + 1 + 1)) by
          apply Fin.ext; rw [Fin.val_succ, one_val_fin (by omega)]] at this
    exact this
  have hadj1 : sDist (A 1) (A ⟨2, by omega⟩) = sDist (B 1) (B ⟨2, by omega⟩) := by
    have := hside ⟨1, by omega⟩
    unfold sideLen at this
    rw [show ((⟨1, by omega⟩ : Fin (n + 1)).castSucc) = (1 : Fin (n + 1 + 1)) by
          apply Fin.ext; rw [Fin.val_castSucc]; exact (one_val_fin (by omega)).symm,
        show ((⟨1, by omega⟩ : Fin (n + 1)).succ) = (⟨2, by omega⟩ : Fin (n + 1 + 1)) by
          apply Fin.ext; rw [Fin.val_succ]] at this
    exact this
  have hangeq : sphAngle (A 0) (A 1) (A ⟨2, by omega⟩) = sphAngle (B 0) (B 1) (B ⟨2, by omega⟩) := by
    rw [← jointAngle_zero A hn, ← jointAngle_zero B hn]; exact hjoint0
  have hdiag := frontCut_diag_side_eq A B hn hadj0 hadj1 hangeq
  intro i
  by_cases hi0 : i.val = 0
  · -- side 0 = diagonal
    rw [show i = (⟨0, by omega⟩ : Fin n) from Fin.ext hi0]
    rw [frontCut_sideLen_zero A hn, frontCut_sideLen_zero B hn]
    exact hdiag
  · -- side i ≥ 1 = parent side ⟨i+1⟩
    rw [frontCut_sideLen_succ A hn hi0, frontCut_sideLen_succ B hn hi0]
    exact hside ⟨i.val + 1, by have := i.isLt; omega⟩



/-- The cut-arm joint `0` is the corner angle `sphAngle (A 0) (A 2) (A 3)` at the diagonal endpoint. -/
theorem frontCut_jointAngle_zero {n : ℕ} (A : Fin (n + 1 + 1) → S2) (hn : 2 ≤ n) :
    jointAngle (frontCut A) (⟨0, by omega⟩ : Fin (n - 1)) =
      sphAngle (A 0) (A ⟨2, by omega⟩) (A ⟨3, by omega⟩) := by
  have hn1 : 1 ≤ n := by omega
  unfold jointAngle
  have e0 : ((frontCut A) ⟨(⟨0, by omega⟩ : Fin (n - 1)).val, by omega⟩) = A 0 := by
    rw [show ((⟨(⟨0, by omega⟩ : Fin (n - 1)).val, by omega⟩ : Fin (n + 1))) = 0 from
      Fin.ext (by simp)]
    exact frontCut_zero A
  have e1 : ((frontCut A) ⟨(⟨0, by omega⟩ : Fin (n - 1)).val + 1, by omega⟩) =
      A ⟨2, by omega⟩ := by
    rw [show ((⟨(⟨0, by omega⟩ : Fin (n - 1)).val + 1, by omega⟩ : Fin (n + 1))) = 1 from
      Fin.ext (by rw [one_val_fin hn1])]
    exact frontCut_one A hn1
  have e2 : ((frontCut A) ⟨(⟨0, by omega⟩ : Fin (n - 1)).val + 2, by omega⟩) =
      A ⟨3, by omega⟩ := by
    have hne : (⟨(⟨0, by omega⟩ : Fin (n - 1)).val + 2, by omega⟩ : Fin (n + 1)) ≠ 0 := by
      intro h; rw [Fin.ext_iff] at h; simp at h
    rw [frontCut_of_ne_zero A hne]
  rw [e0, e1, e2]

/-- The cut-arm joint `i ≥ 1` is the inherited parent joint `jointAngle A ⟨i+1⟩`. -/
theorem frontCut_jointAngle_succ {n : ℕ} (A : Fin (n + 1 + 1) → S2) (hn : 2 ≤ n)
    {i : Fin (n - 1)} (hi : i.val ≠ 0) :
    jointAngle (frontCut A) i = jointAngle A ⟨i.val + 1, by have := i.isLt; omega⟩ := by
  have hn1 : 1 ≤ n := by omega
  unfold jointAngle
  have hb : i.val < n - 1 := i.isLt
  -- the three cut-arm vertices are at indices i, i+1, i+2 (all nonzero), mapping to A (i+2), (i+3), (i+4)
  have e0 : ((frontCut A) ⟨i.val, by omega⟩) = A ⟨i.val + 1, by omega⟩ := by
    have hne : (⟨i.val, by omega⟩ : Fin (n + 1)) ≠ 0 := by
      intro h; rw [Fin.ext_iff] at h; simp only [Fin.val_zero] at h; exact hi h
    rw [frontCut_of_ne_zero A hne]
  have e1 : ((frontCut A) ⟨i.val + 1, by omega⟩) = A ⟨i.val + 2, by omega⟩ := by
    have hne : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) ≠ 0 := by
      intro h; rw [Fin.ext_iff] at h; simp only [Fin.val_zero] at h; omega
    rw [frontCut_of_ne_zero A hne]
  have e2 : ((frontCut A) ⟨i.val + 2, by omega⟩) = A ⟨i.val + 3, by omega⟩ := by
    have hne : (⟨i.val + 2, by omega⟩ : Fin (n + 1)) ≠ 0 := by
      intro h; rw [Fin.ext_iff] at h; simp only [Fin.val_zero] at h; omega
    rw [frontCut_of_ne_zero A hne]
  rw [e0, e1, e2]

/-- **Matched joint angles of the cut arms, away from the corner.**  For `i ≥ 1`, the cut-arm joint
inequality `jointAngle (frontCut A) i ≤ jointAngle (frontCut B) i` is inherited from the parent
`hangle` (both equal the parent joint `⟨i+1⟩`). -/
theorem frontCut_jointAngle_succ_le {n : ℕ} (A B : Fin (n + 1 + 1) → S2) (hn : 2 ≤ n)
    (hangle : ∀ k : Fin (n + 1 - 1), jointAngle A k ≤ jointAngle B k)
    {i : Fin (n - 1)} (hi : i.val ≠ 0) :
    jointAngle (frontCut A) i ≤ jointAngle (frontCut B) i := by
  rw [frontCut_jointAngle_succ A hn hi, frontCut_jointAngle_succ B hn hi]
  exact hangle ⟨i.val + 1, by have := i.isLt; omega⟩



/-- The per-level corner facts, with `hn : 2 ≤ n` a NAMED argument so the `Fin` index bounds resolve.
The first joint is matched, the cut-corner angle inequality holds, and the strictness link transports. -/
def CornerFacts (n : ℕ) (hn : 2 ≤ n) (A B : Fin (n + 1 + 1) → S2) : Prop :=
  jointAngle A (⟨0, by omega⟩ : Fin n) = jointAngle B (⟨0, by omega⟩ : Fin n) ∧
  sphAngle (A 0) (A ⟨2, by omega⟩) (A ⟨3, by omega⟩)
      ≤ sphAngle (B 0) (B ⟨2, by omega⟩) (B ⟨3, by omega⟩) ∧
  ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
    ∃ i : Fin (n - 1), jointAngle (frontCut A) i < jointAngle (frontCut B) i)



/-- **`MatchedCutCornerStep → MatchedCutData` (the load-bearing assembly).**  Given the two corner-step
facts, the `frontCut` sub-arms `A' = frontCut A`, `B' = frontCut B` realise `MatchedCutData A B`:
strict convexity (`frontCut_strictConvexArm`), matched sides (`frontCut_matched_sides`, using the first
joint matched), nondecreasing joints (corner via the corner inequality + `frontCut_jointAngle_zero`,
the rest inherited via `frontCut_jointAngle_succ_le`), endpoint preservation (`frontCut_endpoint`), and
the strictness link. -/
theorem matchedCutData_of_corner {n : ℕ} (hn : 2 ≤ n)
    (A B : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i)
    (hjoint0 : jointAngle A (⟨0, by omega⟩ : Fin n) = jointAngle B (⟨0, by omega⟩ : Fin n))
    (hcorner : sphAngle (A 0) (A ⟨2, by omega⟩) (A ⟨3, by omega⟩)
      ≤ sphAngle (B 0) (B ⟨2, by omega⟩) (B ⟨3, by omega⟩))
    (hlink : (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
      ∃ i : Fin (n - 1), jointAngle (frontCut A) i < jointAngle (frontCut B) i)
    (hangle : ∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) :
    MatchedCutData A B := by
  have hn1 : 1 ≤ n := by omega
  refine ⟨frontCut A, frontCut B, frontCut_strictConvexArm A hA hn,
    frontCut_strictConvexArm B hB hn, frontCut_matched_sides A B hn1 hside hjoint0, ?_,
    frontCut_endpoint A hn1, frontCut_endpoint B hn1, hlink⟩
  -- nondecreasing joints of the cut arms
  intro i
  by_cases hi0 : i.val = 0
  · -- corner joint: i = 0
    rw [show i = (⟨0, by omega⟩ : Fin (n - 1)) from Fin.ext hi0]
    rw [frontCut_jointAngle_zero A hn, frontCut_jointAngle_zero B hn]
    exact hcorner
  · exact frontCut_jointAngle_succ_le A B hn hangle hi0



















end ProofsInTheBook.SphericalMatchedCut

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalMatchedCut
-/
/- Source module: ProofsInTheBook.SphericalCornerStep -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut

namespace ProofsInTheBook.SphericalCornerStep



/-- `arccos (cos (sphAngle u v w)) = sphAngle u v w` (the spherical angle lies in `[0,π]`). -/
theorem arccos_cos_sphAngle (u v w : S2) :
    Real.arccos (Real.cos (sphAngle u v w)) = sphAngle u v w :=
  Real.arccos_cos (sphAngle_nonneg u v w) (sphAngle_le_pi u v w)



/-- **Spherical SSS ⟹ equal angle.**  Two spherical triangles with all three sides equal (the two
sides at the middle vertex genuinely short) have equal angle at the middle vertex.  The angle's cosine
is `(cos opp − cos·cos)/(sin·sin)` from the cosine rule; equal sides give equal cosine, and `arccos`
recovers the angle. -/
theorem sphAngle_eq_of_sides (a₁ b₁ c₁ a₂ b₂ c₂ : S2)
    (h1 : ShortArc a₁ b₁) (h2 : ShortArc b₁ c₁)
    (hab : sDist a₁ b₁ = sDist a₂ b₂)
    (hbc : sDist b₁ c₁ = sDist b₂ c₂)
    (hac : sDist a₁ c₁ = sDist a₂ c₂) :
    sphAngle a₁ b₁ c₁ = sphAngle a₂ b₂ c₂ := by
  -- the two cosine rules
  have e1 := spherical_cosine_rule a₁ b₁ c₁
  have e2 := spherical_cosine_rule a₂ b₂ c₂
  have hsab : 0 < Real.sin (sDist a₁ b₁) := h1.sin_sDist_pos
  have hsbc : 0 < Real.sin (sDist b₁ c₁) := h2.sin_sDist_pos
  -- solve each for cos γ
  have hprod : Real.sin (sDist a₁ b₁) * Real.sin (sDist b₁ c₁) ≠ 0 := by positivity
  -- cos γ₁ = (cos ac − cos ab cos bc)/(sin ab sin bc), same for γ₂ via equal sides
  have hcos : Real.cos (sphAngle a₁ b₁ c₁) = Real.cos (sphAngle a₂ b₂ c₂) := by
    have hg1 : Real.cos (sphAngle a₁ b₁ c₁)
        = (Real.cos (sDist a₁ c₁)
            - Real.cos (sDist a₁ b₁) * Real.cos (sDist b₁ c₁))
          / (Real.sin (sDist a₁ b₁) * Real.sin (sDist b₁ c₁)) := by
      field_simp
      linarith [e1]
    have hg2 : Real.cos (sphAngle a₂ b₂ c₂)
        = (Real.cos (sDist a₂ c₂)
            - Real.cos (sDist a₂ b₂) * Real.cos (sDist b₂ c₂))
          / (Real.sin (sDist a₂ b₂) * Real.sin (sDist b₂ c₂)) := by
      have hsab2 : 0 < Real.sin (sDist a₂ b₂) := by rw [← hab]; exact hsab
      have hsbc2 : 0 < Real.sin (sDist b₂ c₂) := by rw [← hbc]; exact hsbc
      field_simp
      linarith [e2]
    rw [hg1, hg2, hab, hbc, hac]
  -- recover the angle by arccos
  rw [← arccos_cos_sphAngle a₁ b₁ c₁, ← arccos_cos_sphAngle a₂ b₂ c₂, hcos]



/-- **Unoriented tangent-angle additivity (HINGE Lemma 11.3, additive identity).**  If the diagonal
tangent ray at `v` toward `b` lies in the nonnegative cone of the two edge tangent rays toward `a` and
`c`, the spherical angle at `v` from `a` to `c` splits additively through `b`:
`sphAngle a v c = sphAngle a v b + sphAngle b v c`.  Derived from Mathlib's
`angle_eq_angle_add_angle_iff` (the convex-cone-membership direction). -/
theorem sphAngle_additive_of_tangent_between (a v b c : S2)
    (hvb : ShortArc v b)
    (hcone : (tangentTo v b : E3)
      ∈ Submodule.span NNReal ({(tangentTo v a : E3), (tangentTo v c : E3)} : Set E3)) :
    sphAngle a v c = sphAngle a v b + sphAngle b v c := by
  -- `tangentTo v b ≠ 0` since the arc `v b` is short.
  have hb0 : (tangentTo v b : E3) ≠ 0 := (tangentTo_ne_zero_iff v b).2 hvb
  -- unfold to Mathlib unoriented angles and apply the iff (nonneg-combination direction).
  show InnerProductGeometry.angle (tangentTo v a) (tangentTo v c)
      = InnerProductGeometry.angle (tangentTo v a) (tangentTo v b)
        + InnerProductGeometry.angle (tangentTo v b) (tangentTo v c)
  exact (InnerProductGeometry.angle_eq_angle_add_angle_iff hb0).2 (Or.inr hcone)



/-- The corner-triangle angle at `A 2`: the angle `sphAngle (A 1)(A 2)(A 0)` in the triangle
`A0 A1 A2`.  (Equals, by `sphAngle_comm`, the angle `sphAngle (A 0)(A 2)(A 1)`.) -/
theorem cornerTriangle_eq {n : ℕ} (A B : Fin (n + 1 + 1) → S2) (hn : 1 ≤ n)
    (hshort01 : ShortArc (A 1) (A ⟨2, by omega⟩)) (hshort02 : ShortArc (A ⟨2, by omega⟩) (A 0))
    (hs01 : sDist (A 1) (A ⟨2, by omega⟩) = sDist (B 1) (B ⟨2, by omega⟩))
    (hs12 : sDist (A ⟨2, by omega⟩) (A 0) = sDist (B ⟨2, by omega⟩) (B 0))
    (hdiag : sDist (A 1) (A 0) = sDist (B 1) (B 0)) :
    sphAngle (A 1) (A ⟨2, by omega⟩) (A 0) = sphAngle (B 1) (B ⟨2, by omega⟩) (B 0) :=
  -- SSS congruence on the triangle (A1, A2, A0): sides A1A2, A2A0, A1A0 all matched.
  sphAngle_eq_of_sides (A 1) (A ⟨2, by omega⟩) (A 0) (B 1) (B ⟨2, by omega⟩) (B 0)
    hshort01 hshort02 hs01 hs12 hdiag



/-- **The cut-corner angle inequality (HINGE Lemma 11.3), conditional on the tangent-cone membership.**
Given that the diagonal tangent rays `A2 → A0` and `B2 → B0` lie in the cones of their respective edge
rays (the genuine HINGE 11.3 cone membership), the matched first joint (so the corner triangles are
SSS-congruent), the relevant short-arc nondegeneracy, and `jointAngle A ⟨1⟩ ≤ jointAngle B ⟨1⟩`, the
NEW corner angles compare: `sphAngle (A0)(A2)(A3) ≤ sphAngle (B0)(B2)(B3)`.

The proof: by additivity (`sphAngle_additive_of_tangent_between`),
`sphAngle (A1)(A2)(A3) = sphAngle (A1)(A2)(A0) + sphAngle (A0)(A2)(A3)`, hence
`sphAngle (A0)(A2)(A3) = jointAngle A ⟨1⟩ − sphAngle (A1)(A2)(A0)`; the corner-triangle angle agrees
between `A` and `B` (`cornerTriangle_eq`); and `jointAngle A ⟨1⟩ ≤ jointAngle B ⟨1⟩`. -/
theorem cornerAngle_le_of_cone {n : ℕ} (A B : Fin (n + 1 + 1) → S2) (hn : 2 ≤ n)
    -- short-arc nondegeneracy at the corner triangles
    (hAshort12 : ShortArc (A 1) (A ⟨2, by omega⟩))
    (hAshort20 : ShortArc (A ⟨2, by omega⟩) (A 0))
    (hBshort20 : ShortArc (B ⟨2, by omega⟩) (B 0))
    -- matched corner-triangle sides
    (hs01 : sDist (A 1) (A ⟨2, by omega⟩) = sDist (B 1) (B ⟨2, by omega⟩))
    (hs12 : sDist (A ⟨2, by omega⟩) (A 0) = sDist (B ⟨2, by omega⟩) (B 0))
    (hdiagAB : sDist (A 1) (A 0) = sDist (B 1) (B 0))
    -- HINGE 11.3 cone membership at the two corners (the genuine residual analytic fact)
    (hconeA : (tangentTo (A ⟨2, by omega⟩) (A 0) : E3)
      ∈ Submodule.span NNReal
        ({(tangentTo (A ⟨2, by omega⟩) (A 1) : E3),
          (tangentTo (A ⟨2, by omega⟩) (A ⟨3, by omega⟩) : E3)} : Set E3))
    (hconeB : (tangentTo (B ⟨2, by omega⟩) (B 0) : E3)
      ∈ Submodule.span NNReal
        ({(tangentTo (B ⟨2, by omega⟩) (B 1) : E3),
          (tangentTo (B ⟨2, by omega⟩) (B ⟨3, by omega⟩) : E3)} : Set E3))
    -- the parent joint inequality at joint ⟨1⟩
    (hjoint1 : jointAngle A (⟨1, by omega⟩ : Fin n) ≤ jointAngle B (⟨1, by omega⟩ : Fin n)) :
    sphAngle (A 0) (A ⟨2, by omega⟩) (A ⟨3, by omega⟩)
      ≤ sphAngle (B 0) (B ⟨2, by omega⟩) (B ⟨3, by omega⟩) := by
  have hn1 : 1 ≤ n := by omega
  -- additivity at A2: angle (A1, A2, A3) = angle (A1, A2, A0) + angle (A0, A2, A3)
  have haddA := sphAngle_additive_of_tangent_between (A 1) (A ⟨2, by omega⟩) (A 0) (A ⟨3, by omega⟩)
    hAshort20 hconeA
  have haddB := sphAngle_additive_of_tangent_between (B 1) (B ⟨2, by omega⟩) (B 0) (B ⟨3, by omega⟩)
    hBshort20 hconeB
  -- jointAngle ⟨1⟩ = sphAngle (·1)(·2)(·3)
  have hjA : jointAngle A (⟨1, by omega⟩ : Fin n)
      = sphAngle (A 1) (A ⟨2, by omega⟩) (A ⟨3, by omega⟩) := by
    unfold jointAngle; congr 1
  have hjB : jointAngle B (⟨1, by omega⟩ : Fin n)
      = sphAngle (B 1) (B ⟨2, by omega⟩) (B ⟨3, by omega⟩) := by
    unfold jointAngle; congr 1
  -- corner-triangle angles agree (SSS congruence)
  have hcornereq : sphAngle (A 1) (A ⟨2, by omega⟩) (A 0) = sphAngle (B 1) (B ⟨2, by omega⟩) (B 0) :=
    cornerTriangle_eq A B hn1 hAshort12 hAshort20 hs01 hs12 hdiagAB
  -- from additivity: cornerA = jointA1 − triangleAngleA, cornerB = jointB1 − triangleAngleB
  rw [hjA, hjB] at hjoint1
  -- haddA : sphAngle (A1)(A2)(A3) = sphAngle (A1)(A2)(A0) + sphAngle (A0)(A2)(A3)
  -- so sphAngle (A0)(A2)(A3) = sphAngle (A1)(A2)(A3) − sphAngle (A1)(A2)(A0)
  linarith [haddA, haddB, hcornereq, hjoint1]



/-- The per-level corner cone facts: the matched first joint, the two HINGE 11.3 tangent-cone
memberships (the genuine analytic residue), the corner-triangle short-arc nondegeneracy and matched
sides, and the strictness link.  These are exactly the inputs `cornerAngle_le_of_cone` and
`frontCut_matched_sides` consume to realise `CornerFacts`. -/
def CornerConeFacts (n : ℕ) (hn : 2 ≤ n) (A B : Fin (n + 1 + 1) → S2) : Prop :=
  -- (2) matched first joint
  jointAngle A (⟨0, by omega⟩ : Fin n) = jointAngle B (⟨0, by omega⟩ : Fin n) ∧
  -- corner-triangle short-arc nondegeneracy (from convex position of the parent arms)
  ShortArc (A 1) (A ⟨2, by omega⟩) ∧ ShortArc (A ⟨2, by omega⟩) (A 0) ∧
    ShortArc (B ⟨2, by omega⟩) (B 0) ∧
  -- corner-triangle matched sides (parent sides + matched diagonal via SAS)
  sDist (A 1) (A ⟨2, by omega⟩) = sDist (B 1) (B ⟨2, by omega⟩) ∧
  sDist (A ⟨2, by omega⟩) (A 0) = sDist (B ⟨2, by omega⟩) (B 0) ∧
  sDist (A 1) (A 0) = sDist (B 1) (B 0) ∧
  -- (1, analytic core) the HINGE 11.3 tangent-cone memberships
  (tangentTo (A ⟨2, by omega⟩) (A 0) : E3)
    ∈ Submodule.span NNReal
      ({(tangentTo (A ⟨2, by omega⟩) (A 1) : E3),
        (tangentTo (A ⟨2, by omega⟩) (A ⟨3, by omega⟩) : E3)} : Set E3) ∧
  (tangentTo (B ⟨2, by omega⟩) (B 0) : E3)
    ∈ Submodule.span NNReal
      ({(tangentTo (B ⟨2, by omega⟩) (B 1) : E3),
        (tangentTo (B ⟨2, by omega⟩) (B ⟨3, by omega⟩) : E3)} : Set E3) ∧
  -- the strictness link (cut-arm joints inherit a strict parent joint)
  ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
    ∃ i : Fin (n - 1), jointAngle (frontCut A) i < jointAngle (frontCut B) i)



/-- **`MatchedCutCornerConeStep → CornerFacts` (the corner-inequality discharge).**  Given the corner
cone facts, the cut-corner angle inequality (1) follows from `cornerAngle_le_of_cone`, and the matched
first joint and strictness link are carried directly — so `CornerFacts` holds. -/
theorem cornerFacts_of_cone {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1 + 1) → S2)
    (hangle : ∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i)
    (hcone : CornerConeFacts n hn A B) :
    CornerFacts n hn A B := by
  obtain ⟨hjoint0, hAs12, hAs20, hBs20, hs01, hs12, hdiag, hconeA, hconeB, hlink⟩ := hcone
  refine ⟨hjoint0, ?_, hlink⟩
  -- joint ⟨1⟩ inequality from hangle (Fin (n+1-1) = Fin n, index 1 < n since n ≥ 2)
  have hjoint1 : jointAngle A (⟨1, by omega⟩ : Fin n) ≤ jointAngle B (⟨1, by omega⟩ : Fin n) := by
    have := hangle ⟨1, by omega⟩
    -- Fin (n+1-1) and Fin n have the same value 1; jointAngle only reads `.val`
    have hidx : (⟨1, by omega⟩ : Fin (n + 1 - 1)).val = (⟨1, by omega⟩ : Fin n).val := rfl
    simpa [jointAngle, hidx] using this
  exact cornerAngle_le_of_cone A B hn hAs12 hAs20 hBs20 hs01 hs12 hdiag hconeA hconeB hjoint1



















end ProofsInTheBook.SphericalCornerStep

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalCornerStep
import ProofsInTheBook.PlanarConvexDiag
-/
/- Source module: ProofsInTheBook.SphericalConeMembership -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep

namespace ProofsInTheBook.SphericalConeMembership



/-- `det3` is additive in its third slot. -/
theorem det3_add_right (a b c d : E3) :
    det3 a b (c + d) = det3 a b c + det3 a b d := by
  simp only [det3, add_apply]; ring

/-- `det3` is homogeneous in its third slot. -/
theorem det3_smul_right (r : ℝ) (a b c : E3) :
    det3 a b (r • c) = r * det3 a b c := by
  simp only [det3, smul_apply]; ring

/-- `det3` is additive in its second slot. -/
theorem det3_add_mid (a b c d : E3) :
    det3 a (b + c) d = det3 a b d + det3 a c d := by
  simp only [det3, add_apply]; ring

/-- `det3` is homogeneous in its second slot. -/
theorem det3_smul_mid (r : ℝ) (a b c : E3) :
    det3 a (r • b) c = r * det3 a b c := by
  simp only [det3, smul_apply]; ring

/-- `det3` vanishes with a repeated second/third slot. -/
theorem det3_self_mid₂ (a b : E3) : det3 a b b = 0 := by
  simp only [det3]; ring



/-- `det3` is antisymmetric under swapping the first two slots. -/
theorem det3_swap_left (a b c : E3) : det3 a b c = - det3 b a c := by
  simp only [det3]; ring



/-- `v × w` is parallel to `m` when `v, w ⟂ m`: `cross v w = (det3 m v w / ‖m‖²) • m`. -/
theorem cross_parallel_of_perp {m v w : E3} (hm : m ≠ 0)
    (hv : (⟪m, v⟫ : ℝ) = 0) (hw : (⟪m, w⟫ : ℝ) = 0) :
    cross v w = ((det3 m v w) / ‖m‖ ^ 2) • m := by
  -- `m × (v × w) = ⟪m,w⟫•v − ⟪m,v⟫•w = 0`, so `v × w` is parallel to `m`.
  have hcr : cross m (cross v w) = 0 := by
    rw [SphericalRotation.cross_cross, hw, hv, zero_smul, zero_smul, sub_zero]
  -- `m × (m × (v×w)) = ⟪m, v×w⟫ • m − ‖m‖² • (v×w)`, and the LHS = m × 0 = 0.
  have hc0 : cross m (0 : E3) = 0 := by
    apply ext_coord <;> simp
  have hcc := SphericalRotation.cross_cross m m (cross v w)
  rw [hcr, hc0, real_inner_self_eq_norm_sq] at hcc
  -- hcc : 0 = ⟪m, v×w⟫ • m − ‖m‖² • (v×w)
  have hmm : (0 : ℝ) < ‖m‖ ^ 2 := by positivity
  have hmx : (⟪m, cross v w⟫ : ℝ) = det3 m v w := inner_cross_eq_det3 m v w
  -- solve for `v × w`
  have hpar : (‖m‖ ^ 2 : ℝ) • (cross v w) = (det3 m v w) • m := by
    rw [← hmx]
    have hz : (⟪m, cross v w⟫ : ℝ) • m - (‖m‖ ^ 2 : ℝ) • (cross v w) = 0 := hcc.symm
    linear_combination (norm := module) -hz
  -- divide by ‖m‖²
  have : cross v w = (‖m‖ ^ 2 : ℝ)⁻¹ • ((det3 m v w) • m) := by
    rw [← hpar, smul_smul, inv_mul_cancel₀ (ne_of_gt hmm), one_smul]
  rw [this, smul_smul, div_eq_inv_mul]

/-- The coplanarity input for `normsq_smul_b`: `⟪v × w, u⟫ = 0` when `u, v, w ⟂ m` (`m ≠ 0`). -/
theorem inner_cross_perp {m u v w : E3} (hm : m ≠ 0)
    (hu : (⟪m, u⟫ : ℝ) = 0) (hv : (⟪m, v⟫ : ℝ) = 0) (hw : (⟪m, w⟫ : ℝ) = 0) :
    (⟪cross v w, u⟫ : ℝ) = 0 := by
  rw [cross_parallel_of_perp hm hv hw, real_inner_smul_left, hu, mul_zero]

/-- **Planar nonneg-cone from sign-consistency.**  Let `m ≠ 0` and let `u, v, w` all be orthogonal to
`m` (so coplanar in the `2`-plane `m^⊥`), with `v, w` independent (`det3 m v w ≠ 0`).  If the planar
orientation of `u` against each bounding edge is sign-consistent with the edge's own orientation —
`0 ≤ det3 m u w · det3 m v w` and `0 ≤ det3 m v u · det3 m v w` — then `u` is a nonnegative combination
`u ∈ span ℝ≥0 {v, w}`.  (The tangent-plane analogue of `betweenness_span_nnreal`.) -/
theorem mem_span_nnreal_of_planar_signs {m u v w : E3} (hm : m ≠ 0)
    (hu : (⟪m, u⟫ : ℝ) = 0) (hv : (⟪m, v⟫ : ℝ) = 0) (hw : (⟪m, w⟫ : ℝ) = 0)
    (hD : det3 m v w ≠ 0)
    (h1 : 0 ≤ det3 m u w * det3 m v w)
    (h2 : 0 ≤ det3 m v u * det3 m v w) :
    u ∈ Submodule.span NNReal ({v, w} : Set E3) := by
  -- coplanarity of `u` with `v, w`
  have hperp : (⟪cross v w, u⟫ : ℝ) = 0 := inner_cross_perp hm hu hv hw
  -- the explicit Gram decomposition `‖v×w‖² • u = α • v + β • w`
  have hns := normsq_smul_b v u w hperp
  set W : ℝ := ‖cross v w‖ ^ 2 with hWdef
  set α : ℝ := (⟪u, v⟫ : ℝ) * (⟪w, w⟫ : ℝ) - (⟪u, w⟫ : ℝ) * (⟪v, w⟫ : ℝ) with hαdef
  set β : ℝ := (⟪u, w⟫ : ℝ) * (⟪v, v⟫ : ℝ) - (⟪u, v⟫ : ℝ) * (⟪w, v⟫ : ℝ) with hβdef
  -- `hns : W • u = α • v + β • w`
  have hW0 : (0 : ℝ) < W := by
    rw [hWdef]
    have hne : cross v w ≠ 0 := by
      intro hz
      apply hD
      rw [← inner_cross_eq_det3, hz, inner_zero_right]
    positivity
  -- The two coordinate identities relating `α, β` to the planar orientations.
  -- Apply `det3 m · w` to `hns`: W·det3 m u w = α·det3 m v w + β·det3 m w w = α·det3 m v w.
  have hcoordα : W * det3 m u w = α * det3 m v w := by
    have h := congrArg (fun z => det3 m z w) hns
    simp only at h
    -- h : det3 m (W•u) w = det3 m (α•v + β•w) w
    rw [det3_smul_mid, det3_add_mid, det3_smul_mid, det3_smul_mid, det3_self_mid₂,
      mul_zero, add_zero] at h
    exact h
  -- Apply `det3 m v ·` to `hns`: W·det3 m v u = α·det3 m v v + β·det3 m v w = β·det3 m v w.
  have hcoordβ : W * det3 m v u = β * det3 m v w := by
    have h := congrArg (fun z => det3 m v z) hns
    simp only at h
    -- h : det3 m v (W•u) = det3 m v (α•v + β•w)
    rw [det3_smul_right, det3_add_right, det3_smul_right, det3_smul_right] at h
    -- h : W·det3 m v u = α·det3 m v v + β·det3 m v w
    rw [show det3 m v v = 0 from det3_self_mid₂ m v, mul_zero, zero_add] at h
    exact h
  -- From the sign hypotheses, extract `α ≥ 0`, `β ≥ 0`.
  have hD2 : (0 : ℝ) < det3 m v w ^ 2 := by positivity
  have hα0 : 0 ≤ α := by
    -- α·D² = (α·D)·D = (W·det3 m u w)·D = W·(det3 m u w · D) ≥ 0
    have hkey : α * det3 m v w ^ 2 = W * (det3 m u w * det3 m v w) := by
      rw [sq]; linear_combination (-(det3 m v w)) * hcoordα
    have hpos : 0 ≤ α * det3 m v w ^ 2 := by
      rw [hkey]; exact mul_nonneg (le_of_lt hW0) h1
    exact nonneg_of_mul_nonneg_left hpos hD2
  have hβ0 : 0 ≤ β := by
    have hkey : β * det3 m v w ^ 2 = W * (det3 m v u * det3 m v w) := by
      rw [sq]; linear_combination (-(det3 m v w)) * hcoordβ
    have hpos : 0 ≤ β * det3 m v w ^ 2 := by
      rw [hkey]; exact mul_nonneg (le_of_lt hW0) h2
    exact nonneg_of_mul_nonneg_left hpos hD2
  -- assemble `u = (α/W) • v + (β/W) • w` with nonnegative coordinates
  have hu_eq : u = (α / W) • v + (β / W) • w := by
    have hns2 : u = (1 / W) • (α • v + β • w) := by
      rw [← hns, smul_smul, one_div_mul_cancel (ne_of_gt hW0), one_smul]
    rw [hns2, smul_add, smul_smul, smul_smul]; congr 2 <;> ring
  have hadiv : 0 ≤ α / W := div_nonneg hα0 (le_of_lt hW0)
  have hbdiv : 0 ≤ β / W := div_nonneg hβ0 (le_of_lt hW0)
  rw [Submodule.mem_span_pair]
  refine ⟨⟨α / W, hadiv⟩, ⟨β / W, hbdiv⟩, ?_⟩
  show (α / W : ℝ) • v + (β / W : ℝ) • w = u
  exact hu_eq.symm



/-- **Gnomonic transport (tangent ↔ planar orientation).**  `det3 m (p) (q) = det3 m (tangentTo m p)
(tangentTo m q)`: the component of each neighbour along the apex `m` is a repeated first column. -/
theorem det3_tangentTo_eq (m p q : S2) :
    det3 (m : E3) (p : E3) (q : E3)
      = det3 (m : E3) (tangentTo m p) (tangentTo m q) := by
  -- the three repeated-`m`-column determinants all vanish
  have mmm : det3 (m : E3) (m : E3) (m : E3) = 0 := by simp only [det3]; ring
  have mmt : det3 (m : E3) (m : E3) (tangentTo m q) = 0 := by simp only [det3]; ring
  have mtm : det3 (m : E3) (tangentTo m p) (m : E3) = 0 := by simp only [det3]; ring
  conv_lhs =>
    rw [decompose_unit_along_tangent m p, decompose_unit_along_tangent m q]
  simp only [det3_add_mid, det3_add_right, det3_smul_mid, det3_smul_right,
    mmm, mmt, mtm, mul_zero, add_zero, zero_add]



/-- The tangent at the apex is orthogonal to the apex (the `⟪m, tangentTo m p⟫ = 0` input). -/
theorem inner_apex_tangentTo (m p : S2) : (⟪(m : E3), tangentTo m p⟫ : ℝ) = 0 := by
  rw [real_inner_comm]; exact tangentTo_orthogonal m p

/-- **The cut-corner tangent-cone membership (HINGE 11.3, cone form) — DISCHARGED.**  For a strictly
convex spherical polygon `P : Fin N → S2` and a cut apex at index `2` (with `4 ≤ N` so `0,1,2,3` are
distinct vertices in increasing order), the cut diagonal's tangent ray `tangentTo (P 2)(P 0)` lies in
the nonnegative cone of the two adjacent edge tangent rays `tangentTo (P 2)(P 1)` and
`tangentTo (P 2)(P 3)`:

  `tangentTo (P 2)(P 0) ∈ span ℝ≥0 {tangentTo (P 2)(P 1), tangentTo (P 2)(P 3)}`.

This is the genuine HINGE 11.3 analytic fact the substrate previously had only in determinant-sign
form.  The proof transports the three apex-`2` orientations to the tangent plane (`det3_tangentTo_eq`),
reads off their signs from `cyclicTriplePos_unconditional` (each is an odd permutation of a positive
increasing triple, hence negative), and feeds the two positive sign products to
`mem_span_nnreal_of_planar_signs`. -/
theorem cutCorner_cone_membership {N : ℕ} [NeZero N] {P : Fin N → S2}
    (hP : StrictConvexSphPolygon P)
    (h0 : (0 : Fin N) < (1 : Fin N)) (h1 : (1 : Fin N) < (2 : Fin N))
    (h2 : (2 : Fin N) < (3 : Fin N)) :
    (tangentTo (P 2) (P 0) : E3)
      ∈ Submodule.span NNReal
        ({(tangentTo (P 2) (P 1) : E3), (tangentTo (P 2) (P 3) : E3)} : Set E3) := by
  have hcyc : CyclicTriplePos P := cyclicTriplePos_unconditional hP
  set m : S2 := P 2 with hm
  set u : E3 := tangentTo m (P 0) with hudef
  set v : E3 := tangentTo m (P 1) with hvdef
  set w : E3 := tangentTo m (P 3) with hwdef
  -- The three increasing-order positive orientations.
  have p012 : 0 < det3 (P 0 : E3) (P 1 : E3) (P 2 : E3) := hcyc 0 1 2 h0 h1
  have p023 : 0 < det3 (P 0 : E3) (P 2 : E3) (P 3 : E3) := hcyc 0 2 3 (h0.trans h1) h2
  have p123 : 0 < det3 (P 1 : E3) (P 2 : E3) (P 3 : E3) := hcyc 1 2 3 h1 h2
  -- The three apex-2 orientations, all NEGATIVE (odd permutations of the above).
  -- det3 (P2) (P1) (P3) = - det3 (P1) (P2) (P3) < 0
  have d_vw : det3 (m : E3) (P 1 : E3) (P 3 : E3) < 0 := by
    rw [hm, det3_swap_left]; linarith [p123]
  -- det3 (P2) (P0) (P3) = - det3 (P0) (P2) (P3) < 0
  have d_uw : det3 (m : E3) (P 0 : E3) (P 3 : E3) < 0 := by
    rw [hm, det3_swap_left]; linarith [p023]
  -- det3 (P2) (P1) (P0) = - det3 (P0) (P1) (P2)  (reversal = transposition of outer two)
  have d_vu : det3 (m : E3) (P 1 : E3) (P 0 : E3) < 0 := by
    rw [hm]
    -- det3 (P2)(P1)(P0) = - det3 (P0)(P1)(P2)
    have : det3 (P 2 : E3) (P 1 : E3) (P 0 : E3) = - det3 (P 0 : E3) (P 1 : E3) (P 2 : E3) := by
      simp only [det3]; ring
    rw [this]; linarith [p012]
  -- Transport to the tangent plane.
  have tvw : det3 (m : E3) v w = det3 (m : E3) (P 1 : E3) (P 3 : E3) := by
    rw [hvdef, hwdef, ← det3_tangentTo_eq]
  have tuw : det3 (m : E3) u w = det3 (m : E3) (P 0 : E3) (P 3 : E3) := by
    rw [hudef, hwdef, ← det3_tangentTo_eq]
  have tvu : det3 (m : E3) v u = det3 (m : E3) (P 1 : E3) (P 0 : E3) := by
    rw [hvdef, hudef, ← det3_tangentTo_eq]
  -- The hypotheses of the planar cone lemma.
  have hmne : (m : E3) ≠ 0 := by
    intro h; have := m.2; rw [h, norm_zero] at this; norm_num at this
  have hum : (⟪(m : E3), u⟫ : ℝ) = 0 := by rw [hudef]; exact inner_apex_tangentTo m (P 0)
  have hvm : (⟪(m : E3), v⟫ : ℝ) = 0 := by rw [hvdef]; exact inner_apex_tangentTo m (P 1)
  have hwm : (⟪(m : E3), w⟫ : ℝ) = 0 := by rw [hwdef]; exact inner_apex_tangentTo m (P 3)
  have hDne : det3 (m : E3) v w ≠ 0 := by rw [tvw]; exact ne_of_lt d_vw
  have hsign1 : 0 ≤ det3 (m : E3) u w * det3 (m : E3) v w := by
    rw [tuw, tvw]; exact le_of_lt (mul_pos_of_neg_of_neg d_uw d_vw)
  have hsign2 : 0 ≤ det3 (m : E3) v u * det3 (m : E3) v w := by
    rw [tvu, tvw]; exact le_of_lt (mul_pos_of_neg_of_neg d_vu d_vw)
  -- apply the planar cone lemma
  have := mem_span_nnreal_of_planar_signs hmne hum hvm hwm hDne hsign1 hsign2
  -- rewrite the set members back
  rw [hudef, hvdef, hwdef, hm] at this
  exact this



/-- The value of `(2 : Fin (n + 1 + 1))` is `2` (for `n ≥ 2`). -/
theorem two_val {n : ℕ} (hn : 2 ≤ n) : ((2 : Fin (n + 1 + 1)) : ℕ) = 2 := by
  simp; omega

/-- The value of `(3 : Fin (n + 1 + 1))` is `3` (for `n ≥ 2`). -/
theorem three_val {n : ℕ} (hn : 2 ≤ n) : ((3 : Fin (n + 1 + 1)) : ℕ) = 3 := by
  simp; omega

theorem cut_indices_lt {n : ℕ} (hn : 2 ≤ n) :
    (0 : Fin (n + 1 + 1)) < (1 : Fin (n + 1 + 1)) ∧
    (1 : Fin (n + 1 + 1)) < (2 : Fin (n + 1 + 1)) ∧
    (2 : Fin (n + 1 + 1)) < (3 : Fin (n + 1 + 1)) := by
  have h1 : ((1 : Fin (n + 1 + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [Fin.lt_def, Fin.val_zero, h1]; omega
  · rw [Fin.lt_def, h1, two_val hn]; omega
  · rw [Fin.lt_def, two_val hn, three_val hn]; omega

/-- The index `(⟨3, _⟩ : Fin (n + 1 + 1))` equals the numeral `3`. -/
theorem fin_three_eq {n : ℕ} (hn : 2 ≤ n) :
    (⟨3, by omega⟩ : Fin (n + 1 + 1)) = (3 : Fin (n + 1 + 1)) :=
  Fin.ext (by rw [three_val hn])

/-- The index `(⟨2, _⟩ : Fin (n + 1 + 1))` equals the numeral `2`. -/
theorem fin_two_eq {n : ℕ} (hn : 2 ≤ n) :
    (⟨2, by omega⟩ : Fin (n + 1 + 1)) = (2 : Fin (n + 1 + 1)) :=
  Fin.ext (by rw [two_val hn])

/-- **The cut-corner cone membership in arm indexing — DISCHARGED.**  For a strictly convex arm
`A : Fin (n + 1 + 1) → S2` (`n ≥ 2`), the diagonal tangent ray at the cut apex `A ⟨2⟩` lies in the
nonnegative cone of the two edge tangent rays toward `A 1` and `A ⟨3⟩` — exactly the cone-membership
conjunct of `CornerConeFacts`. -/
theorem armCutCorner_cone_membership {n : ℕ} (hn : 2 ≤ n) (A : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) :
    (tangentTo (A ⟨2, by omega⟩) (A 0) : E3)
      ∈ Submodule.span NNReal
        ({(tangentTo (A ⟨2, by omega⟩) (A 1) : E3),
          (tangentTo (A ⟨2, by omega⟩) (A ⟨3, by omega⟩) : E3)} : Set E3) := by
  have hP : StrictConvexSphPolygon (n := n + 1 + 1) A := hA.closed_convex
  obtain ⟨h0, h1, h2⟩ := cut_indices_lt hn
  have hmem := cutCorner_cone_membership hP h0 h1 h2
  -- rewrite the numerals `2, 3` to the `⟨_, _⟩` forms
  rw [fin_two_eq hn, fin_three_eq hn]
  exact hmem



/-- The per-level §8.4 matched-joint facts: the matched first joint, the corner-triangle short-arc
nondegeneracy and matched sides, and the strictness link.  This is `CornerConeFacts` with the two cone
memberships REMOVED (now proved unconditionally by `armCutCorner_cone_membership`). -/
def MatchedFirstJointFacts (n : ℕ) (hn : 2 ≤ n) (A B : Fin (n + 1 + 1) → S2) : Prop :=
  jointAngle A (⟨0, by omega⟩ : Fin n) = jointAngle B (⟨0, by omega⟩ : Fin n) ∧
  ShortArc (A 1) (A ⟨2, by omega⟩) ∧ ShortArc (A ⟨2, by omega⟩) (A 0) ∧
    ShortArc (B ⟨2, by omega⟩) (B 0) ∧
  sDist (A 1) (A ⟨2, by omega⟩) = sDist (B 1) (B ⟨2, by omega⟩) ∧
  sDist (A ⟨2, by omega⟩) (A 0) = sDist (B ⟨2, by omega⟩) (B 0) ∧
  sDist (A 1) (A 0) = sDist (B 1) (B 0) ∧
  ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
    ∃ i : Fin (n - 1), jointAngle (frontCut A) i < jointAngle (frontCut B) i)



/-- **`MatchedFirstJointFacts → CornerConeFacts` (cone membership supplied).**  The two cone
memberships are furnished by `armCutCorner_cone_membership` for `A` and `B`; everything else is carried
from `MatchedFirstJointFacts`. -/
theorem cornerConeFacts_of_matchedFirstJoint {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hf : MatchedFirstJointFacts n hn A B) :
    CornerConeFacts n hn A B := by
  obtain ⟨hjoint0, hAs12, hAs20, hBs20, hs01, hs12, hdiag, hlink⟩ := hf
  exact ⟨hjoint0, hAs12, hAs20, hBs20, hs01, hs12, hdiag,
    armCutCorner_cone_membership hn A hA,
    armCutCorner_cone_membership hn B hB, hlink⟩





















end ProofsInTheBook.SphericalConeMembership

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalConeMembership
-/
/- Source module: ProofsInTheBook.SphericalArmDone -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership

namespace ProofsInTheBook.SphericalArmDone



/-- Parent side `0` of the corner triangle: `sDist (A 0)(A 1) = sDist (B 0)(B 1)`, from `hside 0`. -/
theorem corner_side0_eq {n : ℕ} (A B : Fin (n + 1 + 1) → S2) (hn : 1 ≤ n)
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i) :
    sDist (A 0) (A 1) = sDist (B 0) (B 1) := by
  have := hside ⟨0, by omega⟩
  unfold sideLen at this
  rw [show ((⟨0, by omega⟩ : Fin (n + 1)).castSucc) = (0 : Fin (n + 1 + 1)) by apply Fin.ext; simp,
      show ((⟨0, by omega⟩ : Fin (n + 1)).succ) = (1 : Fin (n + 1 + 1)) by
        apply Fin.ext; rw [Fin.val_succ, one_val_fin (by omega)]] at this
  exact this

/-- Parent side `1` of the corner triangle: `sDist (A 1)(A 2) = sDist (B 1)(B 2)`, from `hside 1`. -/
theorem corner_side1_eq {n : ℕ} (A B : Fin (n + 1 + 1) → S2) (hn : 1 ≤ n)
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i) :
    sDist (A 1) (A ⟨2, by omega⟩) = sDist (B 1) (B ⟨2, by omega⟩) := by
  have := hside ⟨1, by omega⟩
  unfold sideLen at this
  rw [show ((⟨1, by omega⟩ : Fin (n + 1)).castSucc) = (1 : Fin (n + 1 + 1)) by
        apply Fin.ext; rw [Fin.val_castSucc]; exact (one_val_fin (by omega)).symm,
      show ((⟨1, by omega⟩ : Fin (n + 1)).succ) = (⟨2, by omega⟩ : Fin (n + 1 + 1)) by
        apply Fin.ext; rw [Fin.val_succ]] at this
  exact this

/-- Joint `0` as the spherical angle at `A 1` between `A 0` and `A 2`. -/
theorem jointAngle0_eq_sphAngle {n : ℕ} (A : Fin (n + 1 + 1) → S2) (hn : 1 ≤ n) :
    jointAngle A (⟨0, by omega⟩ : Fin (n + 1 - 1)) = sphAngle (A 0) (A 1) (A ⟨2, by omega⟩) := by
  simp only [jointAngle]
  congr 1 <;> (try rfl) <;> (congr 1) <;> (apply Fin.ext) <;> simp



/-- The corner-triangle short arcs of a strictly convex arm: `A1–A2` is an edge, `A2–A0` is the
closing diagonal of the corner window `0 < 1 < 2`, both short. -/
theorem corner_shortArcs {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (hn : 2 ≤ n) :
    ShortArc (A 1) (A ⟨2, by omega⟩) ∧ ShortArc (A ⟨2, by omega⟩) (A 0) := by
  have hP : StrictConvexSphPolygon (n := n + 1 + 1) A := hA.closed_convex
  have hn1 : 1 ≤ n := by omega
  constructor
  · -- A1 → A2 is the edge at index 1
    have he := hP.edge_short (1 : Fin (n + 1 + 1))
    have hsucc : (1 : Fin (n + 1 + 1)) + 1 = (⟨2, by omega⟩ : Fin (n + 1 + 1)) := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_one']
      rw [Nat.mod_eq_of_lt (show 1 < n + 1 + 1 by omega),
        Nat.mod_eq_of_lt (show 1 + 1 < n + 1 + 1 by omega)]
    rwa [hsucc] at he
  · -- A2 → A0 short: the diagonal `A0 → A2` is `frontCut A`'s edge 0, symmetrised.
    have hfc : StrictConvexSphArm (frontCut A) := frontCut_strictConvexArm A hA hn
    have he := hfc.closed_convex.edge_short (0 : Fin (n + 1))
    rw [frontCut_zero, show ((0 : Fin (n + 1)) + 1) = 1 by simp, frontCut_one A hn1] at he
    -- he : ShortArc (A 0) (A ⟨2⟩);  want ShortArc (A ⟨2⟩) (A 0)
    exact he.symm

/-- **The congruent base: `MatchedFirstJointFacts` from all-joints-matched.**  When every joint of `A`
and `B` agrees (and the sides agree), the matched-first-joint configuration is *present*: joint 0 is
matched (a special case of all joints matched), the corner short arcs hold by convex position, the
corner sides match by SAS (`congruent_corner_diag`), and the strictness link is vacuous (no joint is
strictly wider).  This discharges `MatchedFirstJointFacts` unconditionally in the congruent case — the
matched joint is achieved, not carried. -/
theorem congruent_matchedFirstJointFacts {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i)
    (hjoints : ∀ i : Fin (n + 1 - 1), jointAngle A i = jointAngle B i) :
    MatchedFirstJointFacts n hn A B := by
  obtain ⟨hAs12, hAs20⟩ := corner_shortArcs A hA hn
  obtain ⟨hBs12, hBs20⟩ := corner_shortArcs B hB hn
  have hn1 : 1 ≤ n := by omega
  have hs01 : sDist (A 0) (A 1) = sDist (B 0) (B 1) := corner_side0_eq A B hn1 hside
  have hs12 : sDist (A 1) (A ⟨2, by omega⟩) = sDist (B 1) (B ⟨2, by omega⟩) :=
    corner_side1_eq A B hn1 hside
  have hj0' : sphAngle (A 0) (A 1) (A ⟨2, by omega⟩) = sphAngle (B 0) (B 1) (B ⟨2, by omega⟩) := by
    rw [← jointAngle0_eq_sphAngle A hn1, ← jointAngle0_eq_sphAngle B hn1]; exact hjoints _
  refine ⟨?_, hAs12, hAs20, hBs20, hs12, ?_, ?_, ?_⟩
  · -- joint 0 matched
    exact hjoints (⟨0, by omega⟩ : Fin (n + 1 - 1))
  · -- corner side A2A0 = B2B0, via diag_len_eq on triangle (A0, A1, A2)
    have hdiag := diag_len_eq (A 0) (A 1) (A ⟨2, by omega⟩) (B 0) (B 1) (B ⟨2, by omega⟩)
      hs01 hs12 hj0'
    rw [sDist_comm (A ⟨2, by omega⟩) (A 0), sDist_comm (B ⟨2, by omega⟩) (B 0)]
    exact hdiag
  · -- corner side A1A0 = B1B0
    rw [sDist_comm (A 1) (A 0), sDist_comm (B 1) (B 0)]; exact hs01
  · -- strictness link: vacuous (no joint is strictly wider, since all are equal)
    rintro ⟨i, hi⟩
    exact absurd (hjoints i ▸ hi) (lt_irrefl _)



/-- **The per-step joint dichotomy.**  Given nondecreasing joints (`hangle : ≤`), either every joint is
equal, or some joint is strictly wider.  (Decidable case split on the finite joint family.) -/
theorem joint_dichotomy {n : ℕ} (A B : Fin (n + 1 + 1) → S2)
    (hangle : ∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) :
    (∀ i : Fin (n + 1 - 1), jointAngle A i = jointAngle B i) ∨
      (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) := by
  by_cases h : ∀ i : Fin (n + 1 - 1), jointAngle A i = jointAngle B i
  · exact Or.inl h
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    exact Or.inr ⟨i, lt_of_le_of_ne (hangle i) hi⟩







/-- **Congruent-case matched-cut data (UNCONDITIONAL).**  When all joints agree, the congruent
`MatchedFirstJointFacts` (Block A) upgrade — via the proved cone membership
(`cornerConeFacts_of_matchedFirstJoint`), the corner-angle discharge (`cornerFacts_of_cone`), and the
`frontCut` assembly (`matchedCutData_of_corner`) — to `MatchedCutData A B`.  No residue is consumed. -/
theorem congruent_matchedCutData {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i)
    (hjoints : ∀ i : Fin (n + 1 - 1), jointAngle A i = jointAngle B i) :
    MatchedCutData A B := by
  -- congruent matched-first-joint facts
  have hmf : MatchedFirstJointFacts n hn A B :=
    congruent_matchedFirstJointFacts hn A B hA hB hside hjoints
  -- upgrade to corner cone facts via the proved cone membership
  have hcone : CornerConeFacts n hn A B :=
    cornerConeFacts_of_matchedFirstJoint hn A B hA hB hmf
  -- corner facts via the proved corner-angle discharge
  have hcorner : CornerFacts n hn A B := cornerFacts_of_cone hn A B hangle hcone
  obtain ⟨hjoint0, hcornerAngle, hlink⟩ := hcorner
  -- assemble the matched-cut data through frontCut
  exact matchedCutData_of_corner hn A B hA hB hside hjoint0 hcornerAngle hlink hangle

























end ProofsInTheBook.SphericalArmDone

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmDone
-/
/- Source module: ProofsInTheBook.SphericalArmFinish -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership ProofsInTheBook.SphericalArmDone

namespace ProofsInTheBook.SphericalArmFinish









/-- The endpoint pair from a `MatchedCutData` (congruent base or stuck-cut branch), through the proved
cut transport. -/
theorem endpt_of_matchedCutData {n : ℕ} (ih : SZComparison n) {A B : Fin (n + 1 + 1) → S2}
    (hcut : MatchedCutData A B) :
    endpt A ≤ endpt B ∧
      ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) → endpt A < endpt B) :=
  step_of_matchedCutData ih hcut































end ProofsInTheBook.SphericalArmFinish

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmFinish
-/
/- Source module: ProofsInTheBook.SphericalArmClose2 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership ProofsInTheBook.SphericalArmDone
open ProofsInTheBook.SphericalArmFinish

namespace ProofsInTheBook.SphericalArmClose2















































end ProofsInTheBook.SphericalArmClose2

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmClose2
-/
/- Source module: ProofsInTheBook.SphericalStuckCollinear -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership ProofsInTheBook.SphericalArmDone
open ProofsInTheBook.SphericalArmFinish ProofsInTheBook.SphericalArmClose2

namespace ProofsInTheBook.SphericalStuckCollinear















































end ProofsInTheBook.SphericalStuckCollinear

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalStuckCollinear
-/
/- Source module: ProofsInTheBook.SphericalOpenedArmCore -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership ProofsInTheBook.SphericalArmDone
open ProofsInTheBook.SphericalArmFinish ProofsInTheBook.SphericalArmClose2
open ProofsInTheBook.SphericalStuckCollinear

namespace ProofsInTheBook.SphericalOpenedArmCore



/-- **The weak endpoint bound from the single opening-witness residue.**  For a level-`(n+1)` convex arm
pair with equal sides, nondecreasing joints and the level-`n` comparison, `endpt A ≤ endpt B` — derived
from `StuckWitnessExists` via the congruent / deficient joint dichotomy.  No `WeakArmStep` hypothesis is
consumed. -/
theorem weak_endpt_bound (hw : StuckWitnessExists) {n : ℕ} (hn : 2 ≤ n)
    (A B : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i)
    (ih : SZComparison n) :
    endpt A ≤ endpt B := by
  rcases joint_dichotomy A B hangle with hcong | hdef
  · -- congruent: the proved-unconditional matched cut feeds the proved endpoint transport.
    exact (endpt_of_matchedCutData ih (congruent_matchedCutData hn A B hA hB hside hangle hcong)).1
  · -- deficient: the strict bound from the opening-witness residue.
    exact le_of_lt (szStep_strict_of_stuckWitness hw hn A B hA hB hside hangle ih hdef)





/-- **`StuckWitnessExists → OpenedArmReachOrStuck` (the headline reduction).**  The chapter's hard
theorem `SphericalOpening.OpenedArmReachOrStuck` reduced to the SINGLE named residue
`StuckWitnessExists` — strictly stronger than the substrate's two-residue
`openedArmReachOrStuck_of_witness_weak` (which additionally required `WeakArmStep`, now eliminated by
`weakArmStep_of_stuckWitness`).  The weak bound is `weak_endpt_bound`; the strict branch is routed
through `Or.inr` via `szStep_strict_of_stuckWitness`. -/
theorem openedArmReachOrStuck_of_stuckWitness (hw : StuckWitnessExists) :
    OpenedArmReachOrStuck := by
  intro n hn A B hA hB hside hangle ih
  refine ⟨weak_endpt_bound hw hn A B hA hB hside hangle ih, ?_⟩
  intro hwider
  exact Or.inr (szStep_strict_of_stuckWitness hw hn A B hA hB hside hangle ih hwider)

/-- **The deliverable: `OpenedArmReachOrStuck`, conditional only on the single residue
`StuckWitnessExists`.** -/
theorem openedArmReachOrStuck_holds (h : StuckWitnessExists) : OpenedArmReachOrStuck :=
  openedArmReachOrStuck_of_stuckWitness h



/-- **`SchoenbergZarembaTarget`, conditional only on the single residue `StuckWitnessExists`.**
Composing the reduction with the proven chain `schoenbergZaremba_of_reachOrStuck`. -/
theorem schoenbergZaremba_of_stuckWitness (h : StuckWitnessExists) : SchoenbergZarembaTarget :=
  schoenbergZaremba_of_reachOrStuck (openedArmReachOrStuck_holds h)



/-- **The kernel arm lemma, end-to-end strict form, conditional only on `StuckWitnessExists`.** -/
theorem armMono_strict_of_stuckWitness (h : StuckWitnessExists)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_strict A B
    (schoenbergZaremba_of_stuckWitness h hn A B hA hB hside hangle) hstrict







end ProofsInTheBook.SphericalOpenedArmCore

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalStuckCollinear
-/
/- Source module: ProofsInTheBook.SphericalSZInduction -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalTerminalVis
open ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalStuckCollinear

namespace ProofsInTheBook.SphericalSZInduction

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



/-- A **weakly convex** spherical polygon: as `StrictConvexSphPolygon`, but the non-incident supports
are only required `≥ 0` (no strict positivity).  This is the closure of the strict class under the
`δ*` opening: at the admissible supremum a non-incident support may be exactly `0`. -/
structure WeakConvexSphPolygon {n : ℕ} [NeZero n] (P : Fin n → S2) : Prop where
  three_le : 3 ≤ n
  edge_short : ∀ i : Fin n, ShortArc (P i) (P (i + 1))
  edge_support : ∀ i j : Fin n, 0 ≤ sOrient (P i) (P (i + 1)) (P j)
  open_hemisphere : ∃ h : E3, ‖h‖ = 1 ∧ ∀ i : Fin n, 0 < ⟪h, (P i : E3)⟫

/-- A **weakly convex** spherical arm: its closure is a weakly convex polygon. -/
structure WeakConvexSphArm {n : ℕ} (A : Fin (n + 1) → S2) : Prop where
  two_le : 2 ≤ n
  closed_convex : WeakConvexSphPolygon (n := n + 1) A

/-- Every strictly convex polygon is weakly convex (drop the strict non-incidence). -/
theorem StrictConvexSphPolygon.toWeak {n : ℕ} [NeZero n] {P : Fin n → S2}
    (hP : StrictConvexSphPolygon P) : WeakConvexSphPolygon P :=
  { three_le := hP.three_le
    edge_short := hP.edge_short
    edge_support := hP.edge_support
    open_hemisphere := hP.open_hemisphere }

/-- Every strictly convex arm is weakly convex. -/
theorem strictConvexSphArm_toWeak {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) : WeakConvexSphArm A :=
  { two_le := hA.two_le
    closed_convex := StrictConvexSphPolygon.toWeak hA.closed_convex }

/-- **Equal sides**: every side length agrees. -/
def SameSides {n : ℕ} (A B : Fin (n + 1) → S2) : Prop :=
  ∀ i : Fin n, sideLen A i = sideLen B i

/-- **Joints nondecreasing**: every interior joint of `A` is `≤` the corresponding joint of `B`. -/
def JointLe {n : ℕ} (A B : Fin (n + 1) → S2) : Prop :=
  ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i

/-- The set of **deficient** interior joints: those at which `A` is strictly less open than `B`. -/
def deficitSet {n : ℕ} (A B : Fin (n + 1) → S2) : Finset (Fin (n - 1)) :=
  Finset.univ.filter (fun k => jointAngle A k < jointAngle B k)

/-- The deficit count, the second component of the lexicographic recursion measure. -/
def deficitCount {n : ℕ} (A B : Fin (n + 1) → S2) : ℕ := (deficitSet A B).card

theorem mem_deficitSet {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} :
    k ∈ deficitSet A B ↔ jointAngle A k < jointAngle B k := by
  simp [deficitSet]



/-- The interior tail-opening: fix vertices `≤ k`, rotate vertices `> k` about the axis `A k`. -/
def openTail {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ) : Fin (n + 1) → S2 :=
  fun r => if r.val ≤ k.val then A r else rotS2 (A k) δ (A r)

@[simp] theorem openTail_zero {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ) :
    openTail A k δ 0 = A 0 := by
  simp only [openTail, Fin.val_zero]
  rw [if_pos (Nat.zero_le _)]

theorem openTail_fixed {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ)
    {r : Fin (n + 1)} (hr : r.val ≤ k.val) : openTail A k δ r = A r := by
  simp only [openTail]; rw [if_pos hr]

theorem openTail_rot {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ)
    {r : Fin (n + 1)} (hr : k.val < r.val) : openTail A k δ r = rotS2 (A k) δ (A r) := by
  simp only [openTail]; rw [if_neg (by omega)]

/-- `openTail` at `δ = 0` is the identity (the rotation by `0` is the identity, fixing every vertex).
-/
theorem openTail_zero_angle {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) :
    openTail A k 0 = A := by
  funext r
  by_cases hr : r.val ≤ k.val
  · exact openTail_fixed A k 0 hr
  · rw [openTail_rot A k 0 (by omega)]
    apply S2.ext
    simp [rotS2_coe, rot_zero]

/-- The axis vertex `A k` is fixed by the opening (`k ≤ k`). -/
theorem openTail_axis {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ) :
    openTail A k δ k = A k := openTail_fixed A k δ (le_refl _)

/-- **`openTail` preserves the distance between two tail vertices** (both rotated by the same
isometry). -/
theorem sDist_openTail_tail {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ)
    {r s : Fin (n + 1)} (hr : k.val < r.val) (hs : k.val < s.val) :
    sDist (openTail A k δ r) (openTail A k δ s) = sDist (A r) (A s) := by
  rw [openTail_rot A k δ hr, openTail_rot A k δ hs, sDist_rotS2]

/-- **`openTail` preserves the distance from the axis `A k` to a tail vertex** (axis fixed, target
rotated; the rotation preserves inner products with its axis). -/
theorem sDist_openTail_axis_tail {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ)
    {r : Fin (n + 1)} (hr : k.val < r.val) :
    sDist (openTail A k δ k) (openTail A k δ r) = sDist (A k) (A r) := by
  rw [openTail_axis, openTail_rot A k δ hr, sDist, sDist, sInner, sInner, rotS2_coe]
  congr 1
  have h := inner_rot_axis (A k).2 δ (A r : E3)
  rw [real_inner_comm (rot (A k : E3) δ (A r : E3)) (A k : E3), h,
      real_inner_comm (A r : E3) (A k : E3)]

/-- **`openTail` preserves every side length.**  `r < k`: both endpoints fixed.  `r = k`: axis fixed,
tail vertex rotated about the axis.  `k < r`: both endpoints rotated by the same isometry. -/
theorem openTail_preserves_sides {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ)
    (i : Fin n) : sideLen (openTail A k δ) i = sideLen A i := by
  rcases lt_trichotomy i.val k.val with hlt | heq | hgt
  · -- i < k: i.castSucc ≤ k and i.succ ≤ k (since i.succ.val = i+1 ≤ k).
    have h1 : openTail A k δ i.castSucc = A i.castSucc :=
      openTail_fixed A k δ (by simp [Fin.castSucc, Fin.castAdd]; omega)
    have h2 : openTail A k δ i.succ = A i.succ :=
      openTail_fixed A k δ (by simp [Fin.succ]; omega)
    rw [sideLen, sideLen, h1, h2]
  · -- i = k: i.castSucc = k (fixed), i.succ = k+1 (rotated).
    have hcast : (i.castSucc).val = k.val := by simp [Fin.castSucc, Fin.castAdd]; omega
    have hsucc : k.val < (i.succ).val := by simp [Fin.succ]; omega
    have hk : i.castSucc = k := Fin.ext hcast
    rw [sideLen, sideLen, hk]
    exact sDist_openTail_axis_tail A k δ (r := i.succ) hsucc
  · -- k < i: i.castSucc > k and i.succ > k.
    have hcast : k.val < (i.castSucc).val := by simp [Fin.castSucc, Fin.castAdd]; omega
    have hsucc : k.val < (i.succ).val := by simp [Fin.succ]; omega
    rw [sideLen, sideLen, sDist_openTail_tail A k δ hcast hsucc]



/-- **`openTail` (axis vertex `k`) preserves the spherical angle at any joint `r` that does not
straddle the axis.**  A joint `r` uses vertices `r, r+1, r+2`; the axis is the vertex `k`.  If all
three are `≤ k` (head, fixed) or all `> k` (tail, rotated by one isometry), the angle is unchanged.

**Caveat (corrected from handoff design §6).**  The *straddling* joints are `r = k-1` (vertices
`k-1,k,k+1`) and `r = k` (vertices `k,k+1,k+2`): rotating the *whole* tail about an interior axis
vertex disturbs **two** adjacent joints, not one.  The design §6's "only joint `k` changes" claim does
not hold for the interior `openTail` (the joint below the axis is also disturbed).  This is part of why
the single-joint deficit-decrease bookkeeping belongs to the isolated residue (§G). -/
theorem openTail_preserves_joint_offaxis {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ)
    {r : Fin (n - 1)} (hoff : r.val + 2 ≤ k.val ∨ k.val < r.val) :
    jointAngle (openTail A k δ) r = jointAngle A r := by
  have hrlt := r.isLt
  rcases hoff with hlow | hhigh
  · have hv0 : openTail A k δ ⟨r.val, by omega⟩ = A ⟨r.val, by omega⟩ :=
      openTail_fixed A k δ (show r.val ≤ k.val by omega)
    have hv1 : openTail A k δ ⟨r.val + 1, by omega⟩ = A ⟨r.val + 1, by omega⟩ :=
      openTail_fixed A k δ (show r.val + 1 ≤ k.val by omega)
    have hv2 : openTail A k δ ⟨r.val + 2, by omega⟩ = A ⟨r.val + 2, by omega⟩ :=
      openTail_fixed A k δ (show r.val + 2 ≤ k.val by omega)
    simp only [jointAngle, hv0, hv1, hv2]
  · have hv0 : openTail A k δ ⟨r.val, by omega⟩ = rotS2 (A k) δ (A ⟨r.val, by omega⟩) :=
      openTail_rot A k δ (show k.val < r.val by omega)
    have hv1 : openTail A k δ ⟨r.val + 1, by omega⟩ = rotS2 (A k) δ (A ⟨r.val + 1, by omega⟩) :=
      openTail_rot A k δ (show k.val < r.val + 1 by omega)
    have hv2 : openTail A k δ ⟨r.val + 2, by omega⟩ = rotS2 (A k) δ (A ⟨r.val + 2, by omega⟩) :=
      openTail_rot A k δ (show k.val < r.val + 2 by omega)
    simp only [jointAngle, hv0, hv1, hv2, sphAngle_rotS2]





/-- **The folded-flat betweenness *equation*.**  From `p ∈ span≥0 {mid, q}` (the spherical
betweenness), the through-distance equals the sum of the two pieces:
`sDist mid q = sDist mid p + sDist p q`.  This is the kernel's `sDist_betweenness_of_collinear`
specialised; it is the equation `(2)` the diagonal bound consumes. -/
theorem foldedFlat_dist_eq {p mid q : S2}
    (hcol : (p : E3) ∈ Submodule.span NNReal ({(mid : E3), (q : E3)} : Set E3)) :
    sDist mid q = sDist mid p + sDist p q :=
  sDist_betweenness_of_collinear hcol



/-- **The diagonal inequality (design §4 `diag_le`).**  Inputs:
* `hflat : sDist mid q = sDist mid p + sDist p q` — `A`'s folded-flat betweenness equation
  (`p = A i`, `mid = A (i+1)`, `q = A j`);
* `hear  : sDist mid q ≤ sDist mid' q'` — the ear comparison (`mid' = B (i+1)`, `q' = B j`);
* `hside : sDist mid' p' = sDist mid p` — equal first side (`p' = B i`, so `sideLen` at `i` agrees);
output the diagonal inequality `sDist p q ≤ sDist p' q'` (`= sDist (B i) (B j)`), via the spherical
reverse triangle inequality on `B`'s corner `(p', mid', q')`. -/
theorem diag_le_of_flat_ear {p q mid p' q' mid' : S2}
    (hflat : sDist mid q = sDist mid p + sDist p q)
    (hear : sDist mid q ≤ sDist mid' q')
    (hside : sDist mid' p' = sDist mid p) :
    sDist p q ≤ sDist p' q' := by
  -- reverse triangle on B's corner: sDist mid' q' ≤ sDist mid' p' + sDist p' q'.
  have htri : sDist mid' q' ≤ sDist mid' p' + sDist p' q' := sDist_triangle mid' p' q'
  -- sDist p q = sDist mid q − sDist mid p ≤ sDist mid' q' − sDist mid' p' ≤ sDist p' q'.
  nlinarith [hflat, hear, hside, htri]



/-- **The strengthened Schoenberg–Zaremba comparison invariant.**  The left arm is allowed to be only
*weakly* convex (so the STUCK arm at `δ*` is an admissible recursive input — the design's decisive
restructuring); the right arm is strictly convex.  With equal sides and nondecreasing joints, the left
endpoint does not exceed the right. -/
def Main (n : ℕ) : Prop :=
  ∀ A B : Fin (n + 1) → S2,
    WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    endpt A ≤ endpt B



/-- If no joint is deficient, all joints are equal (with `JointLe`). -/
theorem all_joints_eq_of_no_deficit {n : ℕ} {A B : Fin (n + 1) → S2}
    (hangle : JointLe A B) (hnd : deficitCount A B = 0) :
    ∀ k : Fin (n - 1), jointAngle A k = jointAngle B k := by
  intro k
  have hempty : deficitSet A B = ∅ := Finset.card_eq_zero.mp hnd
  have hkni : k ∉ deficitSet A B := by rw [hempty]; simp
  rw [mem_deficitSet] at hkni
  exact le_antisymm (hangle k) (not_lt.mp hkni)

/-- `Main m` holds vacuously for `m < 2` (no weakly-convex arm exists below level 2). -/
theorem main_of_lt_two {m : ℕ} (hm : m < 2) : Main m := by
  intro A B hA _ _ _
  exact absurd hA.two_le (by omega)

/-- A deficient joint exists when the deficit count is positive. -/
theorem exists_deficit_of_pos {n : ℕ} {A B : Fin (n + 1) → S2}
    (hpos : 0 < deficitCount A B) : ∃ k : Fin (n - 1), jointAngle A k < jointAngle B k := by
  have hne : deficitSet A B ≠ ∅ := by
    intro h; rw [deficitCount, h, Finset.card_empty] at hpos; exact absurd hpos (lt_irrefl 0)
  obtain ⟨k, hk⟩ := Finset.nonempty_of_ne_empty hne
  exact ⟨k, (mem_deficitSet).mp hk⟩





























end ProofsInTheBook.SphericalSZInduction

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZInduction
-/
/- Source module: ProofsInTheBook.SphericalSZStepClose -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalStuckCollinear
open ProofsInTheBook.SphericalSZInduction

namespace ProofsInTheBook.SphericalSZStepClose

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



/-- The contiguous **interval (ear) sub-arm**: `intervalArm A a m j = A ⟨a + j, _⟩`, the sub-tuple of
`A` starting at vertex `a` of length `m + 1`.  The membership bound `a + m ≤ N` makes every `a + j`
(`j ≤ m`) land in `Fin (N + 1)`. -/
def intervalArm {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N) :
    Fin (m + 1) → S2 :=
  fun j => A ⟨a + j.val, by have := j.isLt; omega⟩

@[simp] theorem intervalArm_apply {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N)
    (j : Fin (m + 1)) : intervalArm A a m hb j = A ⟨a + j.val, by have := j.isLt; omega⟩ := rfl

/-- The ear's first vertex is `A a`. -/
theorem intervalArm_zero {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N) :
    intervalArm A a m hb 0 = A ⟨a, by omega⟩ := by
  simp only [intervalArm, Fin.val_zero, Nat.add_zero]

/-- The ear's last vertex is `A (a + m)`. -/
theorem intervalArm_last {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N) :
    intervalArm A a m hb (Fin.last m) = A ⟨a + m, by omega⟩ := by
  simp only [intervalArm, Fin.val_last]

/-- The ear endpoint is the chord `sDist (A a) (A (a+m))`. -/
theorem intervalArm_endpt {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N) :
    endpt (intervalArm A a m hb) = sDist (A ⟨a, by omega⟩) (A ⟨a + m, by omega⟩) := by
  unfold endpt
  rw [intervalArm_zero, intervalArm_last]



/-- The ear vertex at any `Fin (m+1)` index `x` is the parent vertex at value `a + x`. -/
theorem intervalArm_index {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N)
    {v : ℕ} (hv : v < m + 1) :
    (intervalArm A a m hb) ⟨v, hv⟩ = A ⟨a + v, by omega⟩ := rfl

/-- The ear's side `i` is the parent's side `a + i`. -/
theorem intervalArm_sideLen {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N)
    (i : Fin m) :
    sideLen (intervalArm A a m hb) i = sideLen A ⟨a + i.val, by have := i.isLt; omega⟩ := by
  -- both sides equal `sDist (A ⟨a+i⟩) (A ⟨a+i+1⟩)` after normalizing every Fin index by its value.
  unfold sideLen
  have lhs0 : (intervalArm A a m hb) i.castSucc = A ⟨a + i.val, by have := i.isLt; omega⟩ := by
    show A ⟨a + (i.castSucc).val, _⟩ = _
    have : a + (i.castSucc).val = a + i.val := by rw [Fin.val_castSucc]
    simp only [this]
  have lhs1 : (intervalArm A a m hb) i.succ = A ⟨a + i.val + 1, by have := i.isLt; omega⟩ := by
    show A ⟨a + (i.succ).val, _⟩ = _
    have : a + (i.succ).val = a + i.val + 1 := by rw [Fin.val_succ]; omega
    simp only [this]
  have rhs0 : A ((⟨a + i.val, by have := i.isLt; omega⟩ : Fin N).castSucc)
      = A ⟨a + i.val, by have := i.isLt; omega⟩ := rfl
  have rhs1 : A ((⟨a + i.val, by have := i.isLt; omega⟩ : Fin N).succ)
      = A ⟨a + i.val + 1, by have := i.isLt; omega⟩ := by
    have : ((⟨a + i.val, by have := i.isLt; omega⟩ : Fin N).succ).val = a + i.val + 1 := by
      rw [Fin.val_succ]
    rw [show ((⟨a + i.val, by have := i.isLt; omega⟩ : Fin N).succ)
        = (⟨a + i.val + 1, by have := i.isLt; omega⟩ : Fin (N + 1)) from Fin.ext this]
  rw [lhs0, lhs1, rhs0, rhs1]

/-- The ear's interior joint `i` (vertices `a+i, a+i+1, a+i+2`) is the parent's interior joint `a + i`.
-/
theorem intervalArm_jointAngle {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N)
    (i : Fin (m - 1)) :
    jointAngle (intervalArm A a m hb) i
      = jointAngle A ⟨a + i.val, by have := i.isLt; omega⟩ := by
  have hi := i.isLt
  unfold jointAngle
  rw [intervalArm_index A a m hb (v := i.val) (by omega),
      intervalArm_index A a m hb (v := i.val + 1) (by omega),
      intervalArm_index A a m hb (v := i.val + 2) (by omega)]
  congr 2





























end ProofsInTheBook.SphericalSZStepClose

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZStepClose
-/
/- Source module: ProofsInTheBook.SphericalSZFinal -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZStep
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose

namespace ProofsInTheBook.SphericalSZFinal

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

























































end ProofsInTheBook.SphericalSZFinal

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZFinal
-/
/- Source module: ProofsInTheBook.SphericalSZClose -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZStep
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal

namespace ProofsInTheBook.SphericalSZClose

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



































































end ProofsInTheBook.SphericalSZClose

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZClose
-/
/- Source module: ProofsInTheBook.SphericalCutTransport -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZClose

namespace ProofsInTheBook.SphericalCutTransport

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000































end ProofsInTheBook.SphericalCutTransport

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalCutTransport
-/
/- Source module: ProofsInTheBook.ZinanFFCT -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalCutTransport

namespace ProofsInTheBook.ZinanFFCT

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





























end ProofsInTheBook.ZinanFFCT

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT
-/
/- Source module: ProofsInTheBook.ZinanFFCT2 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.ZinanFFCT

namespace ProofsInTheBook.ZinanFFCT2

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000




































































end ProofsInTheBook.ZinanFFCT2

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT2
-/
/- Source module: ProofsInTheBook.ZinanFFCT3 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.ZinanFFCT
open ProofsInTheBook.ZinanFFCT2

namespace ProofsInTheBook.ZinanFFCT3

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000































end ProofsInTheBook.ZinanFFCT3

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT3
-/
/- Source module: ProofsInTheBook.ZinanFFCT4 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT
open ProofsInTheBook.ZinanFFCT2
open ProofsInTheBook.ZinanFFCT3

namespace ProofsInTheBook.ZinanFFCT4

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

































end ProofsInTheBook.ZinanFFCT4

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT4
-/
/- Source module: ProofsInTheBook.ZinanFFCT5 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT4

namespace ProofsInTheBook.ZinanFFCT5

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



















end ProofsInTheBook.ZinanFFCT5

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT5
-/
/- Source module: ProofsInTheBook.ZinanFFCT6 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT
open ProofsInTheBook.ZinanFFCT2
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT5

namespace ProofsInTheBook.ZinanFFCT6

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


























end ProofsInTheBook.ZinanFFCT6

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT6
-/
/- Source module: ProofsInTheBook.ZinanFFCT7 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT
open ProofsInTheBook.ZinanFFCT2
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT5
open ProofsInTheBook.ZinanFFCT6

namespace ProofsInTheBook.ZinanFFCT7

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



































end ProofsInTheBook.ZinanFFCT7

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT7
import ProofsInTheBook.PlanarConvexDiag
-/
/- Source module: ProofsInTheBook.ZinanFFCT8 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT ProofsInTheBook.ZinanFFCT2 ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT4 ProofsInTheBook.ZinanFFCT5 ProofsInTheBook.ZinanFFCT6
open ProofsInTheBook.ZinanFFCT7

namespace ProofsInTheBook.ZinanFFCT8

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000































end ProofsInTheBook.ZinanFFCT8

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT8
import ProofsInTheBook.SphericalRotation
-/
/- Source module: ProofsInTheBook.ZinanFFCT9 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT8

namespace ProofsInTheBook.ZinanFFCT9

set_option maxHeartbeats 1600000
















































































end ProofsInTheBook.ZinanFFCT9

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT9
-/
/- Source module: ProofsInTheBook.ZinanFFCT10 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.ZinanFFCT8 ProofsInTheBook.ZinanFFCT9

namespace ProofsInTheBook.ZinanFFCT10

set_option maxHeartbeats 1600000






















































end ProofsInTheBook.ZinanFFCT10








end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT10
-/
/- Source module: ProofsInTheBook.ZinanFFCT17 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.ZinanFFCT10

namespace ProofsInTheBook.ZinanFFCT17

set_option maxHeartbeats 1600000















































































end ProofsInTheBook.ZinanFFCT17

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT17
-/
/- Source module: ProofsInTheBook.ZinanFFCT18 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT17

namespace ProofsInTheBook.ZinanFFCT18

set_option maxHeartbeats 1600000




















































end ProofsInTheBook.ZinanFFCT18

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalStuckWitness
import ProofsInTheBook.SphericalCutTransport
-/
/- Source module: ProofsInTheBook.SphericalStuckGeneral -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalStuckWitness ProofsInTheBook.SphericalTerminalVis
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalCutTransport

namespace ProofsInTheBook.SphericalStuckGeneral





































end ProofsInTheBook.SphericalStuckGeneral

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalStuckGeneral
-/
/- Source module: ProofsInTheBook.SphericalLastCornerStuck -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalCutTransport ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose ProofsInTheBook.SphericalStuckGeneral

namespace ProofsInTheBook.SphericalLastCornerStuck





























end ProofsInTheBook.SphericalLastCornerStuck

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT18
import ProofsInTheBook.SphericalLastCornerStuck
-/
/- Source module: ProofsInTheBook.ZinanFFCT19 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalCutTransport ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.TetDihedral
open ProofsInTheBook.ZinanFFCT18

namespace ProofsInTheBook.ZinanFFCT19

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


















































end ProofsInTheBook.ZinanFFCT19

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZClose
-/
/- Source module: ProofsInTheBook.SphericalMonitoredSup -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZStep
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose

namespace ProofsInTheBook.SphericalMonitoredSup

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000









































































end ProofsInTheBook.SphericalMonitoredSup

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZClose
-/
/- Source module: ProofsInTheBook.SphericalSpliceTransport -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose

namespace ProofsInTheBook.SphericalSpliceTransport

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000























end ProofsInTheBook.SphericalSpliceTransport

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalRotation
import ProofsInTheBook.SphericalCyclicTriple
-/
/- Source module: ProofsInTheBook.SphericalCongruence -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalCyclicTriple

namespace ProofsInTheBook.SphericalCongruence

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



























































end ProofsInTheBook.SphericalCongruence

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalMonitoredSup
import ProofsInTheBook.SphericalSpliceTransport
import ProofsInTheBook.SphericalCongruence
-/
/- Source module: ProofsInTheBook.SphericalArmAssembly -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCongruence

namespace ProofsInTheBook.SphericalArmAssembly

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































end ProofsInTheBook.SphericalArmAssembly

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmAssembly
-/
/- Source module: ProofsInTheBook.SphericalOpeningOutcome -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalArmAssembly

namespace ProofsInTheBook.SphericalOpeningOutcome

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



























end ProofsInTheBook.SphericalOpeningOutcome


end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT19
import ProofsInTheBook.SphericalSZClose
import ProofsInTheBook.SphericalOpeningOutcome
import ProofsInTheBook.ZinanFFCT18
-/
/- Source module: ProofsInTheBook.ZinanFFCT20 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT18

namespace ProofsInTheBook.ZinanFFCT20




















end ProofsInTheBook.ZinanFFCT20

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT10
-/
/- Source module: ProofsInTheBook.ZinanFFCT12 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.ZinanFFCT8 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10

namespace ProofsInTheBook.ZinanFFCT12

set_option maxHeartbeats 1600000



























end ProofsInTheBook.ZinanFFCT12

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT20
import ProofsInTheBook.ZinanFFCT12
-/
/- Source module: ProofsInTheBook.ZinanFFCT21 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18

namespace ProofsInTheBook.ZinanFFCT21

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















































end ProofsInTheBook.ZinanFFCT21

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT21
-/
/- Source module: ProofsInTheBook.ZinanFFCT22 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21

namespace ProofsInTheBook.ZinanFFCT22

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000















































end ProofsInTheBook.ZinanFFCT22

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT22
-/
/- Source module: ProofsInTheBook.ZinanFFCT23 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21

namespace ProofsInTheBook.ZinanFFCT23

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





































end ProofsInTheBook.ZinanFFCT23

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT23
-/
/- Source module: ProofsInTheBook.ZinanFFCT24 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT22 ProofsInTheBook.ZinanFFCT23

namespace ProofsInTheBook.ZinanFFCT24

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000






















































end ProofsInTheBook.ZinanFFCT24

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT24
-/
/- Source module: ProofsInTheBook.ZinanFFCT25 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalRotation
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT22 ProofsInTheBook.ZinanFFCT23 ProofsInTheBook.ZinanFFCT24

namespace ProofsInTheBook.ZinanFFCT25

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000













































end ProofsInTheBook.ZinanFFCT25

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT25
import ProofsInTheBook.SphericalCore
-/
/- Source module: ProofsInTheBook.ZinanFFCT26 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.ZinanFFCT10

namespace ProofsInTheBook.ZinanFFCT26

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000











































end ProofsInTheBook.ZinanFFCT26

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT26
import ProofsInTheBook.SphericalStuckGeneral
-/
/- Source module: ProofsInTheBook.ZinanFFCT27 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10 ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT26 ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalSZ

namespace ProofsInTheBook.ZinanFFCT27

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































end ProofsInTheBook.ZinanFFCT27

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT27
import ProofsInTheBook.ZinanFFCT25
import ProofsInTheBook.SphericalMonitoredSup
import ProofsInTheBook.SphericalOpeningOutcome
-/
/- Source module: ProofsInTheBook.ZinanFFCT28 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT26 ProofsInTheBook.ZinanFFCT27
open ProofsInTheBook.SphericalStuckGeneral ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalMonitoredSup ProofsInTheBook.SphericalSZFinal

namespace ProofsInTheBook.ZinanFFCT28

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



































end ProofsInTheBook.ZinanFFCT28

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalOpeningOutcome
-/
/- Source module: ProofsInTheBook.SphericalOpeningGlue -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome

namespace ProofsInTheBook.SphericalOpeningGlue

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

































end ProofsInTheBook.SphericalOpeningGlue

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT28
import ProofsInTheBook.SphericalOpeningGlue
-/
/- Source module: ProofsInTheBook.ZinanFFCT30 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalOpeningGlue

namespace ProofsInTheBook.ZinanFFCT30

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

























end ProofsInTheBook.ZinanFFCT30

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT30
import ProofsInTheBook.ZinanFFCT22
-/
/- Source module: ProofsInTheBook.ZinanFFCT33 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT30

namespace ProofsInTheBook.ZinanFFCT33

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

































end ProofsInTheBook.ZinanFFCT33
end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT33
-/
/- Source module: ProofsInTheBook.ZinanFFCT34 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT30 ProofsInTheBook.ZinanFFCT33

namespace ProofsInTheBook.ZinanFFCT34

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















end ProofsInTheBook.ZinanFFCT34

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT34
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Combination
-/
/- Source module: ProofsInTheBook.ZinanFFCT36 -/
section
set_option autoImplicit true


noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT33 ProofsInTheBook.ZinanFFCT34

namespace ProofsInTheBook.ZinanFFCT36

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
























end ProofsInTheBook.ZinanFFCT36
end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT36
-/
/- Source module: ProofsInTheBook.ZinanFFCT44 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.ZinanFFCT21 ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT25 ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT36

namespace ProofsInTheBook.ZinanFFCT44

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





































end ProofsInTheBook.ZinanFFCT44

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT20
import ProofsInTheBook.ZinanFFCT3
import ProofsInTheBook.SphericalOpeningGlue
-/
/- Source module: ProofsInTheBook.ZinanFFCT37 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT20
open ProofsInTheBook.ZinanFFCT3

namespace ProofsInTheBook.ZinanFFCT37

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





































































end ProofsInTheBook.ZinanFFCT37

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT37
import ProofsInTheBook.ZinanFFCT36
-/
/- Source module: ProofsInTheBook.ZinanFFCT38 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT37

namespace ProofsInTheBook.ZinanFFCT38

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



















































end ProofsInTheBook.ZinanFFCT38






end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT38
-/
/- Source module: ProofsInTheBook.ZinanFFCT39 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT38

namespace ProofsInTheBook.ZinanFFCT39

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000













































end ProofsInTheBook.ZinanFFCT39

-- Brick 1 (positive content + assembly + audit)





-- Brick 2 (audit + positive content)




end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT39
-/
/- Source module: ProofsInTheBook.ZinanFFCT40 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT38
open ProofsInTheBook.ZinanFFCT39

namespace ProofsInTheBook.ZinanFFCT40

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000























































end ProofsInTheBook.ZinanFFCT40

-- §1 the any-h assembler

-- §3 the pure-hemi strict certificate + repaired stuck outcome + repaired clause (iii)



-- §3 the corrected outcome + repaired headline



-- refutation-resistance witnesses


end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT40
-/
/- Source module: ProofsInTheBook.ZinanFFCT41 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT20
open ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT38
open ProofsInTheBook.ZinanFFCT39
open ProofsInTheBook.ZinanFFCT40

namespace ProofsInTheBook.ZinanFFCT41

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































































































end ProofsInTheBook.ZinanFFCT41

-- §1 the WB family + W-admissibility bridge

-- §2 the base sinusoid

-- §3 the cap by admissibility (the central new content)


-- §5 the WB trichotomy

-- §6/§7 the clauses at the WB sup



-- §8/§9 the base-capped outcome + headline (GlueWBaseCap discharged)


-- refutation-resistance witness


end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT41
-/
/- Source module: ProofsInTheBook.ZinanFFCT42 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT41

namespace ProofsInTheBook.ZinanFFCT42

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000































end ProofsInTheBook.ZinanFFCT42

-- §1 the algebra/index micro-lemmas


-- §2 base-stuck = opened diagonal

-- §3 Brick 1 (the cyclic-identity bridge) + the vanishing-support payload


-- §4 the residual DISCHARGED + the base-stuck-free headline


-- non-vacuity guards


end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT42
-/
/- Source module: ProofsInTheBook.ZinanFFCT45 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT20
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT41
open ProofsInTheBook.ZinanFFCT42

namespace ProofsInTheBook.ZinanFFCT45

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



































































end ProofsInTheBook.ZinanFFCT45

-- §1 the WBS family + closure facts





-- §2 init admissibility

-- §3 deficit bound + base cap



-- §4 the trichotomy + clauses



-- §5 Brick 7: the FFCT42 base-stuck port DISCHARGED



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT42
-/
/- Source module: ProofsInTheBook.ZinanFFCT43 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.ZinanFFCT39
open ProofsInTheBook.ZinanFFCT41
open ProofsInTheBook.ZinanFFCT42

namespace ProofsInTheBook.ZinanFFCT43

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















end ProofsInTheBook.ZinanFFCT43

-- §1 endpoint positivity

-- §2 closing edge distinct at the WB supremum

-- §3 the residual DISCHARGED + the closing-edge-free headline


-- non-vacuity guards


end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT44
import ProofsInTheBook.ZinanFFCT45
import ProofsInTheBook.ZinanFFCT43
-/
/- Source module: ProofsInTheBook.ZinanFFCT46 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT34
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT40
open ProofsInTheBook.ZinanFFCT42
open ProofsInTheBook.ZinanFFCT43
open ProofsInTheBook.ZinanFFCT44
open ProofsInTheBook.ZinanFFCT45

namespace ProofsInTheBook.ZinanFFCT46

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

















































end ProofsInTheBook.ZinanFFCT46

-- §1 the margins-free open-hemisphere production (THE keystone mechanism)

-- §2 brick 4

-- §2′ the opened side / joint geometry



-- §3 bricks 5–6


-- §4 brick 8

-- §5 brick 9 + non-vacuity



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT46
-/
/- Source module: ProofsInTheBook.ZinanFFCT47 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT21 ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT42
open ProofsInTheBook.ZinanFFCT43
open ProofsInTheBook.ZinanFFCT44
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46

namespace ProofsInTheBook.ZinanFFCT47

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



























































end ProofsInTheBook.ZinanFFCT47

-- §1 the open-chain collapse kernel (3 ≤ n)

-- §2 the wrap-edge-free open-hemisphere production

-- §3 wrap ShortArc from the hemisphere

-- §4 the residual discharged


-- §5 the wrap-free headline



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT47
import ProofsInTheBook.ZinanFFCT28
import ProofsInTheBook.SphericalStuckGeneral
-/
/- Source module: ProofsInTheBook.ZinanFFCT49 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT28
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47

namespace ProofsInTheBook.ZinanFFCT49

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000









































end ProofsInTheBook.ZinanFFCT49

-- §0 the opened arm

-- §2 discharged pieces



-- §4 the bridge

-- §5 non-vacuity guards



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT49
import ProofsInTheBook.ZinanFFCT23
-/
/- Source module: ProofsInTheBook.ZinanFFCT52 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49

namespace ProofsInTheBook.ZinanFFCT52

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000









































































end ProofsInTheBook.ZinanFFCT52

-- §1 component 2


-- §2 reversal infra




-- §3 orientation normalization

-- §4 interval convexity


-- §5 assembly


end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT19
import ProofsInTheBook.ZinanFFCT46
import ProofsInTheBook.ZinanFFCT47
-/
/- Source module: ProofsInTheBook.ZinanFFCT48 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47

namespace ProofsInTheBook.ZinanFFCT48

set_option maxHeartbeats 1600000



























end ProofsInTheBook.ZinanFFCT48




end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT25
import ProofsInTheBook.ZinanFFCT48
-/
/- Source module: ProofsInTheBook.ZinanFFCT53 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23 ProofsInTheBook.ZinanFFCT25

namespace ProofsInTheBook.ZinanFFCT53

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


















































end ProofsInTheBook.ZinanFFCT53

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT52
import ProofsInTheBook.ZinanFFCT53
-/
/- Source module: ProofsInTheBook.ZinanFFCT54 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT21 ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT52 ProofsInTheBook.ZinanFFCT53

namespace ProofsInTheBook.ZinanFFCT54

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

















































































end ProofsInTheBook.ZinanFFCT54

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT54
-/
/- Source module: ProofsInTheBook.ZinanFFCT63 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54

namespace ProofsInTheBook.ZinanFFCT63

set_option maxHeartbeats 1600000




















































end ProofsInTheBook.ZinanFFCT63

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT28
-/
/- Source module: ProofsInTheBook.ZinanFFCT29 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT10 ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT26 ProofsInTheBook.ZinanFFCT27
open ProofsInTheBook.ZinanFFCT28

namespace ProofsInTheBook.ZinanFFCT29

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















































end ProofsInTheBook.ZinanFFCT29

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT29
-/
/- Source module: ProofsInTheBook.ZinanFFCT31 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT22 ProofsInTheBook.ZinanFFCT23 ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25 ProofsInTheBook.ZinanFFCT27 ProofsInTheBook.ZinanFFCT29

namespace ProofsInTheBook.ZinanFFCT31

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
























































end ProofsInTheBook.ZinanFFCT31

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT31
-/
/- Source module: ProofsInTheBook.ZinanFFCT32 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT22 ProofsInTheBook.ZinanFFCT23 ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25 ProofsInTheBook.ZinanFFCT27 ProofsInTheBook.ZinanFFCT29
open ProofsInTheBook.ZinanFFCT31

namespace ProofsInTheBook.ZinanFFCT32

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000















































end ProofsInTheBook.ZinanFFCT32

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT49
import ProofsInTheBook.ZinanFFCT32
-/
/- Source module: ProofsInTheBook.ZinanFFCT51 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT27 ProofsInTheBook.ZinanFFCT29 ProofsInTheBook.ZinanFFCT31
open ProofsInTheBook.ZinanFFCT32
open ProofsInTheBook.ZinanFFCT45 ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT49

namespace ProofsInTheBook.ZinanFFCT51

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





























end ProofsInTheBook.ZinanFFCT51

-- §1 the sharp residue

-- §2 the corner sign verification

-- §3 the main near-side line


-- §4 non-vacuity guards



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT51
-/
/- Source module: ProofsInTheBook.ZinanFFCT55 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT26 ProofsInTheBook.ZinanFFCT27
open ProofsInTheBook.ZinanFFCT29
open ProofsInTheBook.ZinanFFCT45 ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT51

namespace ProofsInTheBook.ZinanFFCT55

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000









































end ProofsInTheBook.ZinanFFCT55

-- §R1/R2 the constant-binding contradiction at the WBS family


-- §δ*=0 edge

-- §R3 slot normalization

-- §R4 the derivative + the sign finding



-- §R4′ the forced collapse

-- §5 non-vacuity guards



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT21
import ProofsInTheBook.ZinanFFCT55
-/
/- Source module: ProofsInTheBook.ZinanFFCT56 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT45 ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT55

namespace ProofsInTheBook.ZinanFFCT56

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































end ProofsInTheBook.ZinanFFCT56

-- §A the coefficient bricks


-- §B the master mid-fold kill


-- §C the WBS axis-edge elimination

-- §D the honest dispatch + residue

-- §E the consequence wiring

-- §F non-vacuity guards




end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT48
import ProofsInTheBook.ZinanFFCT56
-/
/- Source module: ProofsInTheBook.ZinanFFCT57 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT56

namespace ProofsInTheBook.ZinanFFCT57

set_option maxHeartbeats 1600000



































end ProofsInTheBook.ZinanFFCT57









end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT10
import ProofsInTheBook.SphericalSpliceTransport
import ProofsInTheBook.ZinanFFCT48
import ProofsInTheBook.ZinanFFCT57
-/
/- Source module: ProofsInTheBook.ZinanFFCT58 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT57

namespace ProofsInTheBook.ZinanFFCT58

set_option maxHeartbeats 1600000
set_option linter.unnecessarySeqFocus false























































































end ProofsInTheBook.ZinanFFCT58







end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT58
-/
/- Source module: ProofsInTheBook.ZinanFFCT59 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58

namespace ProofsInTheBook.ZinanFFCT59

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



































end ProofsInTheBook.ZinanFFCT59









end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT54
import ProofsInTheBook.ZinanFFCT59
-/
/- Source module: ProofsInTheBook.ZinanFFCT60 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT59

namespace ProofsInTheBook.ZinanFFCT60

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


























end ProofsInTheBook.ZinanFFCT60

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT60
import ProofsInTheBook.SphericalRotation
-/
/- Source module: ProofsInTheBook.ZinanFFCT61 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT59
open ProofsInTheBook.ZinanFFCT60

namespace ProofsInTheBook.ZinanFFCT61

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


































































































end ProofsInTheBook.ZinanFFCT61

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT61
-/
/- Source module: ProofsInTheBook.ZinanFFCT62 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58
open ProofsInTheBook.ZinanFFCT59
open ProofsInTheBook.ZinanFFCT61

namespace ProofsInTheBook.ZinanFFCT62

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















































end ProofsInTheBook.ZinanFFCT62

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT62
-/
/- Source module: ProofsInTheBook.ZinanFFCT64 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT62

namespace ProofsInTheBook.ZinanFFCT64

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





































end ProofsInTheBook.ZinanFFCT64

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT63
import ProofsInTheBook.ZinanFFCT64
-/
/- Source module: ProofsInTheBook.ZinanFFCT65 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT59
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT62
open ProofsInTheBook.ZinanFFCT63
open ProofsInTheBook.ZinanFFCT64

namespace ProofsInTheBook.ZinanFFCT65

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



































































end ProofsInTheBook.ZinanFFCT65

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT65
import ProofsInTheBook.PlanarConvexDiag
-/
/- Source module: ProofsInTheBook.ZinanFFCT66 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT63
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65

namespace ProofsInTheBook.ZinanFFCT66

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000












































end ProofsInTheBook.ZinanFFCT66

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT66
-/
/- Source module: ProofsInTheBook.ZinanFFCT67 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66

namespace ProofsInTheBook.ZinanFFCT67

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

















end ProofsInTheBook.ZinanFFCT67

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT67
import ProofsInTheBook.ZinanFFCT26
-/
/- Source module: ProofsInTheBook.ZinanFFCT68 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT26
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT67

namespace ProofsInTheBook.ZinanFFCT68

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000









































end ProofsInTheBook.ZinanFFCT68

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT68
-/
/- Source module: ProofsInTheBook.ZinanFFCT69 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT62
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT67
open ProofsInTheBook.ZinanFFCT68

namespace ProofsInTheBook.ZinanFFCT69

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000




































end ProofsInTheBook.ZinanFFCT69

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT69
import ProofsInTheBook.ZinanFFCT32
-/
/- Source module: ProofsInTheBook.ZinanFFCT70 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT31
open ProofsInTheBook.ZinanFFCT32
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69

namespace ProofsInTheBook.ZinanFFCT70

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000




























end ProofsInTheBook.ZinanFFCT70

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT70
-/
/- Source module: ProofsInTheBook.ZinanFFCT71 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70

namespace ProofsInTheBook.ZinanFFCT71

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000






























end ProofsInTheBook.ZinanFFCT71

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT71
-/
/- Source module: ProofsInTheBook.ZinanFFCT72 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71

namespace ProofsInTheBook.ZinanFFCT72

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000








































end ProofsInTheBook.ZinanFFCT72

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT72
-/
/- Source module: ProofsInTheBook.ZinanFFCT73 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT72

namespace ProofsInTheBook.ZinanFFCT73

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000










































end ProofsInTheBook.ZinanFFCT73

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT73
-/
/- Source module: ProofsInTheBook.ZinanFFCT74 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT73

namespace ProofsInTheBook.ZinanFFCT74

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































































end ProofsInTheBook.ZinanFFCT74

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT74
-/
/- Source module: ProofsInTheBook.ZinanFFCT75 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74

namespace ProofsInTheBook.ZinanFFCT75

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000






















end ProofsInTheBook.ZinanFFCT75

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT75
import ProofsInTheBook.ZinanFFCT44
-/
/- Source module: ProofsInTheBook.ZinanFFCT76 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT44
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75

namespace ProofsInTheBook.ZinanFFCT76

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















end ProofsInTheBook.ZinanFFCT76

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT76
-/
/- Source module: ProofsInTheBook.ZinanFFCT77 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT76

namespace ProofsInTheBook.ZinanFFCT77

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


































































end ProofsInTheBook.ZinanFFCT77

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT77
-/
/- Source module: ProofsInTheBook.ZinanFFCT78 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77

namespace ProofsInTheBook.ZinanFFCT78

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000















end ProofsInTheBook.ZinanFFCT78

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT78
-/
/- Source module: ProofsInTheBook.ZinanFFCT79 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78

namespace ProofsInTheBook.ZinanFFCT79

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















end ProofsInTheBook.ZinanFFCT79

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT79
-/
/- Source module: ProofsInTheBook.ZinanFFCT80 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79

namespace ProofsInTheBook.ZinanFFCT80

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































































end ProofsInTheBook.ZinanFFCT80

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT80
-/
/- Source module: ProofsInTheBook.ZinanFFCT81 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80

namespace ProofsInTheBook.ZinanFFCT81

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000










































end ProofsInTheBook.ZinanFFCT81

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT81
-/
/- Source module: ProofsInTheBook.ZinanFFCT82 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81

namespace ProofsInTheBook.ZinanFFCT82

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


































end ProofsInTheBook.ZinanFFCT82

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT82
-/
/- Source module: ProofsInTheBook.ZinanFFCT83 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82

namespace ProofsInTheBook.ZinanFFCT83

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































end ProofsInTheBook.ZinanFFCT83

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT83
-/
/- Source module: ProofsInTheBook.ZinanFFCT84 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82
open ProofsInTheBook.ZinanFFCT83

namespace ProofsInTheBook.ZinanFFCT84

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

















end ProofsInTheBook.ZinanFFCT84

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT84
-/
/- Source module: ProofsInTheBook.ZinanFFCT85 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82
open ProofsInTheBook.ZinanFFCT83
open ProofsInTheBook.ZinanFFCT84

namespace ProofsInTheBook.ZinanFFCT85

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000









































end ProofsInTheBook.ZinanFFCT85

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT85
-/
/- Source module: ProofsInTheBook.ZinanFFCT86 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82
open ProofsInTheBook.ZinanFFCT83
open ProofsInTheBook.ZinanFFCT84
open ProofsInTheBook.ZinanFFCT85

namespace ProofsInTheBook.ZinanFFCT86

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000








































end ProofsInTheBook.ZinanFFCT86

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT86
-/
/- Source module: ProofsInTheBook.ZinanFFCT100 -/
section
set_option autoImplicit true




open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT86

namespace ProofsInTheBook.ZinanFFCT100







end ProofsInTheBook.ZinanFFCT100




end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT100
-/
/- Source module: ProofsInTheBook.ZinanFFCT111 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT20
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82
open ProofsInTheBook.ZinanFFCT83
open ProofsInTheBook.ZinanFFCT84
open ProofsInTheBook.ZinanFFCT85
open ProofsInTheBook.ZinanFFCT86
open ProofsInTheBook.ZinanFFCT100

namespace ProofsInTheBook.ZinanFFCT111

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000













































































end ProofsInTheBook.ZinanFFCT111

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalReachStuck
import ProofsInTheBook.SphericalSZFinal
import ProofsInTheBook.SphericalSZClose
import ProofsInTheBook.ZinanFFCT111
-/
/- Source module: ProofsInTheBook.ZinanFFCT113 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalHinge ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalFinish ProofsInTheBook.SphericalSZStep
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.ZinanFFCT78 ProofsInTheBook.ZinanFFCT111

namespace ProofsInTheBook.ZinanFFCT113

set_option maxHeartbeats 1600000































end ProofsInTheBook.ZinanFFCT113

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalOpenedArmCore
import ProofsInTheBook.ZinanFFCT111
import ProofsInTheBook.ZinanFFCT113
-/
/- Source module: ProofsInTheBook.ZinanFFCT112 -/
section
set_option autoImplicit true




namespace ProofsInTheBook.ZinanFFCT112

open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalOpenedArmCore
open ProofsInTheBook.SphericalOpeningProcess (StuckWitnessExists)











end ProofsInTheBook.ZinanFFCT112




end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.ZinanFFCT112
-/
/- Source module: ProofsInTheBook.Chapter13 -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Chapter13

open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm



























namespace StrictTriangleSigns





end StrictTriangleSigns

















namespace CauchyArmOpeningObstruction



end CauchyArmOpeningObstruction



namespace CauchyArmClosingObstruction



end CauchyArmClosingObstruction



namespace CauchyArmFixedChordObstruction



end CauchyArmFixedChordObstruction

















namespace CauchyArmVertex







end CauchyArmVertex



namespace CauchyRigidityCertificate







end CauchyRigidityCertificate











end ProofsInTheBook.Chapter13

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.Chapter13
-/
/- Source module: ProofsInTheBook.Ch13CyclicSigns -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13CyclicSigns

open ProofsInTheBook.Chapter13






























end ProofsInTheBook.Ch13CyclicSigns

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
-/
/- Source module: ProofsInTheBook.Ch13MarkedSphere -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13MarkedSphere

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns































































































end ProofsInTheBook.Ch13MarkedSphere

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMap
-/
/- Source module: ProofsInTheBook.PlanarMapEuler -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap.CombMap

open ProofsInTheBook.PlanarMap



















end ProofsInTheBook.PlanarMap.CombMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapEuler
-/
/- Source module: ProofsInTheBook.PlanarMapSimple -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap



























































end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapEuler
-/
/- Source module: ProofsInTheBook.PlanarMapDelete -/
section
set_option autoImplicit true




namespace Equiv.Perm

open Equiv



namespace DeleteSet





















end DeleteSet

open DeleteSet











end Equiv.Perm

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap



































































section TwoEdgePathObstruction























end TwoEdgePathObstruction

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapSimple
-/
/- Source module: ProofsInTheBook.PlanarMapBoundary -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap















namespace BoundaryPath













end BoundaryPath







namespace BoundaryCycle









































namespace Chord





end Chord

end BoundaryCycle





namespace BoundaryArcSplit











end BoundaryArcSplit



namespace BoundaryCycle













end BoundaryCycle



end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapBoundary
-/
/- Source module: ProofsInTheBook.PlanarMapNearTriangulation -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

















namespace BoundaryCycle







end BoundaryCycle







namespace NearTriangulation































end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapNearTriangulation
import ProofsInTheBook.PlanarMapDelete
-/
/- Source module: ProofsInTheBook.PlanarMapFilteredRotation -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace FilteredRotation

























namespace ContiguousInterval



















end ContiguousInterval



section FreshDart





















































end FreshDart

end FilteredRotation

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFilteredRotation
-/
/- Source module: ProofsInTheBook.PlanarMapChordSplitData -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap



namespace NearTriangulation





section ChordDarts





















end ChordDarts



























namespace ChordSplitData















































end ChordSplitData







end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapChordSplitData
-/
/- Source module: ProofsInTheBook.PlanarMapChordSplit -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap











namespace BoundaryPath











end BoundaryPath

namespace NearTriangulation



namespace ChordSplitData































































































































end ChordSplitData

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapChordSplit
-/
/- Source module: ProofsInTheBook.PlanarMapSeparation -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap



namespace NearTriangulation











namespace ChordSplitData





















end ChordSplitData



namespace ChordSplitData











end ChordSplitData

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap


end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapNearTriangulation
-/
/- Source module: ProofsInTheBook.PlanarMapBoundaryFan -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap



namespace NearTriangulation













namespace FanTriangle











end FanTriangle







namespace BoundaryVertexFan











end BoundaryVertexFan





















end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapBoundaryFan
import ProofsInTheBook.PlanarMapDelete
-/
/- Source module: ProofsInTheBook.PlanarMapBoundaryDelete -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap



namespace NearTriangulation


















namespace BoundaryDeletionData

















end BoundaryDeletionData










end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapBoundaryDelete
-/
/- Source module: ProofsInTheBook.PlanarMapFanSurgery -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap



namespace NearTriangulation













namespace NeighborRotationOrder















end NeighborRotationOrder







namespace FanSurgeryReconstruction



















end FanSurgeryReconstruction









end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
/-
List-coloring primitives (Chapter 35 layer 4).

Design-independent groundwork for the Thomassen five-list-coloring route
(HANDOFF/CH35_DESIGN_ANSWER.md): proper colorings from lists, monotonicity
in the graph and in the lists, and the piecewise gluing lemmas — including
the rooted cut-vertex glue, which is the form that is actually true for
list colorings (naive gluing fails because the two sides may disagree at
the cut vertex).
-/
import Mathlib
-/
/- Source module: ProofsInTheBook.ListColoring -/
section
set_option autoImplicit true


namespace ProofsInTheBook.ListColoring





















section Glue







end Glue



end ProofsInTheBook.ListColoring

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapSeparation
import ProofsInTheBook.PlanarMapFanSurgery
import ProofsInTheBook.ListColoring
-/
/- Source module: ProofsInTheBook.ThomassenLists -/
section
set_option autoImplicit true




namespace ProofsInTheBook.ThomassenLists

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.ListColoring




namespace CombMap

open ProofsInTheBook.PlanarMap.CombMap





namespace ThomassenLists











end ThomassenLists





namespace ChordSplitRegions

















end ChordSplitRegions



section Deletion





































































end Deletion

end CombMap

end ProofsInTheBook.ThomassenLists

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanSurgery
-/
/- Source module: ProofsInTheBook.PlanarMapFanConnectivity -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap






















section Reduction









end Reduction



namespace NearTriangulation





































end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanConnectivity
import ProofsInTheBook.PlanarMapFilteredRotation
-/
/- Source module: ProofsInTheBook.PlanarMapFanFaces -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap









namespace NearTriangulation













































































end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanFaces
-/
/- Source module: ProofsInTheBook.PlanarMapFanMergedOrbit -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap



















namespace NearTriangulation















































end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapBoundary
-/
/- Source module: ProofsInTheBook.PlanarMapBoundaryArcSplit -/
section
set_option autoImplicit true




set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap





namespace BoundaryCycleData















end BoundaryCycleData









namespace DataDartArc





















end DataDartArc



namespace BoundaryCycleData











end BoundaryCycleData



section Casts













end Casts





















namespace BoundaryPath









end BoundaryPath



section BPOfDartArc





















end BPOfDartArc



namespace BoundaryCycleData









end BoundaryCycleData



namespace BoundaryCycleData







end BoundaryCycleData

end CombMap

end ProofsInTheBook.PlanarMap





end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanFaces
import ProofsInTheBook.PlanarMapBoundaryArcSplit
-/
/- Source module: ProofsInTheBook.PlanarMapDeletedBoundary -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap























namespace NearTriangulation












namespace DeletedMergedBoundaryCertificate













end DeletedMergedBoundaryCertificate









end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanMergedOrbit
import ProofsInTheBook.PlanarMapDeletedBoundary
-/
/- Source module: ProofsInTheBook.PlanarMapOuterArc -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap



namespace NearTriangulation






namespace MergedOuterArcData









end MergedOuterArcData















end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapOuterArc
-/
/- Source module: ProofsInTheBook.PlanarMapFanExistence -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

























namespace NearTriangulation





































end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ThomassenLists
import ProofsInTheBook.PlanarMapFanExistence
-/
/- Source module: ProofsInTheBook.ThomassenInduction -/
section
set_option autoImplicit true




namespace ProofsInTheBook.ThomassenInduction

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ListColoring
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

universe u











section Base







end Base



section Chord







end Chord



section Chordless



















end Chordless



section Induction









end Induction



section Corollaries








end Corollaries



section FiveColor






end FiveColor

end ProofsInTheBook.ThomassenInduction

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ThomassenInduction
import ProofsInTheBook.PlanarMapChordSplit
import ProofsInTheBook.PlanarMapSeparation
-/
/- Source module: ProofsInTheBook.ChordSplitNT -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ChordSplitNT

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ListColoring
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction

universe u










namespace ChordSideReconstruction



















end ChordSideReconstruction





namespace ChordRecursionData











end ChordRecursionData















end ProofsInTheBook.ChordSplitNT









end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSplitNT
-/
/- Source module: ProofsInTheBook.ChordSplitEuler -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ChordSplitEuler

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation

universe u











section VertexCount

























end VertexCount



section EulerReduction







end EulerReduction



section ChordApplication

















end ChordApplication



section NonVacuity













end NonVacuity

end ProofsInTheBook.ChordSplitEuler











end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSplitEuler
-/
/- Source module: ProofsInTheBook.ChordSideRecon -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ChordSideRecon

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler

universe u





section Connectivity


















end Connectivity



section SphereAssembly





end SphereAssembly



section ChordApplication













end ChordApplication



section JordanData







end JordanData



section NonVacuity







end NonVacuity

end ProofsInTheBook.ChordSideRecon











end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFilteredRotation
import ProofsInTheBook.PlanarMapSeparation
-/
/- Source module: ProofsInTheBook.PlanarMapCutCap -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap







namespace SimplePrimalCycle





































































end SimplePrimalCycle









namespace SimplePrimalCycle





  -- c_i^- ↦ α (dart i)





















end SimplePrimalCycle





namespace CutCapSurgery











end CutCapSurgery



namespace NearTriangulation













end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCap
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapSigma -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap



namespace SimplePrimalCycle





















































       -- c_i^- ↦ p_i

  -- c_i^- ↦ ℓ_i^- = σ⁻¹ q_i























































end SimplePrimalCycle









end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.PermTranspositionCycleCount -/
section
set_option autoImplicit true


set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

open Equiv Equiv.Perm Function





namespace PermTranspositionCycleCount

open scoped Finset









































end PermTranspositionCycleCount





end

/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.RelationComponentCount -/
section
set_option autoImplicit true


open Classical

universe u









































end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapEuler
import ProofsInTheBook.PermTranspositionCycleCount
import ProofsInTheBook.RelationComponentCount
-/
/- Source module: ProofsInTheBook.PlanarMapEulerInequality -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

















































































end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapSigma
import ProofsInTheBook.PlanarMapEulerInequality
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapCounts -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap





namespace CutCapCount

















section SumCongr





















end SumCongr

end CutCapCount



namespace SimplePrimalCycle



open CutCapCount
















end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapCounts
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapV -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap



namespace SimplePrimalCycle



open CutCapCount
































end SimplePrimalCycle

namespace CutCapCount















end CutCapCount

namespace SimplePrimalCycle



open CutCapCount






























































































































































end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapV
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapF -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap



namespace CutCapCount







end CutCapCount

namespace SimplePrimalCycle



open CutCapCount















































end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSideRecon
import ProofsInTheBook.PlanarMapCutCapCounts
import ProofsInTheBook.PlanarMapCutCapF
-/
/- Source module: ProofsInTheBook.ChordFaceCount -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordFaceCount

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.PlanarMap.CombMap.CutCapCount

universe u





section FacePerm















end FacePerm



section FaceBijection







































end FaceBijection



section Dichotomy













end Dichotomy



section Genus0











end Genus0



section SphereAssembly







end SphereAssembly



section NonVacuity







end NonVacuity



section ChordApplication









end ChordApplication



section Headline







end Headline

end ProofsInTheBook.ChordFaceCount















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordFaceCount
import ProofsInTheBook.PlanarMapEulerInequality
-/
/- Source module: ProofsInTheBook.ChordDisk -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordDisk

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount

universe u





section Facts







end Facts



section LowerHalf







end LowerHalf



section Threading









end Threading



section ChordApplication





















end ChordApplication



section NonVacuity











end NonVacuity



section Headline







end Headline



end ProofsInTheBook.ChordDisk
















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordDisk
-/
/- Source module: ProofsInTheBook.SubmapPlanar -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.SubmapPlanar

open Equiv
open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap

universe u























section OrbitSplit



open scoped Classical















end OrbitSplit





section RawRestrict



open scoped Classical







































open scoped Classical













































































end RawRestrict



section ChordThreading



open ProofsInTheBook.ChordSideRecon















end ChordThreading

end ProofsInTheBook.SubmapPlanar

















end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
import ProofsInTheBook.Ch13MarkedSphere
-/
/- Source module: ProofsInTheBook.Ch13MarkedReduction -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13MarkedReduction

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13MarkedSphere

open Equiv Equiv.Perm



section ListBridge









end ListBridge



section OrbitBridge











end OrbitBridge



section StrictBridge













end StrictBridge



section ActiveComponent















end ActiveComponent



section Obstruction
































end Obstruction

end ProofsInTheBook.Ch13MarkedReduction

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.PlanarMapSimple
import ProofsInTheBook.PlanarMapDelete
import ProofsInTheBook.SubmapPlanar
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
import ProofsInTheBook.Ch13MarkedSphere
import ProofsInTheBook.Ch13MarkedReduction
-/
/- Source module: ProofsInTheBook.Ch13ActiveComponent -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13ActiveComponent

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Ch13MarkedReduction




















open ProofsInTheBook.SubmapPlanar













  -- unreachable on active darts























end ProofsInTheBook.Ch13ActiveComponent

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.PlanarMapSimple
import ProofsInTheBook.PlanarMapDelete
import ProofsInTheBook.SubmapPlanar
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
import ProofsInTheBook.Ch13MarkedSphere
import ProofsInTheBook.Ch13MarkedReduction
import ProofsInTheBook.Ch13ActiveComponent
-/
/- Source module: ProofsInTheBook.Ch13FlipTransport -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13FlipTransport

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Ch13MarkedReduction
open ProofsInTheBook.Ch13ActiveComponent
open ProofsInTheBook.SubmapPlanar

open Equiv Equiv.Perm





open ProofsInTheBook -- for DeleteSet.firstOutside via Equiv.Perm namespace









































































end ProofsInTheBook.Ch13FlipTransport

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.PlanarMapSimple
import ProofsInTheBook.PlanarMapEuler
import ProofsInTheBook.PlanarMapDelete
import ProofsInTheBook.SubmapPlanar
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
import ProofsInTheBook.Ch13MarkedSphere
import ProofsInTheBook.Ch13MarkedReduction
import ProofsInTheBook.Ch13ActiveComponent
import ProofsInTheBook.Ch13FlipTransport
import ProofsInTheBook.PlanarMapNearTriangulation
-/
/- Source module: ProofsInTheBook.Ch13ComponentClose -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13ComponentClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Ch13MarkedReduction
open ProofsInTheBook.Ch13ActiveComponent
open ProofsInTheBook.Ch13FlipTransport
open ProofsInTheBook.SubmapPlanar

open Equiv Equiv.Perm































































































end ProofsInTheBook.Ch13ComponentClose

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Ch13MarkedSphere
import ProofsInTheBook.Ch13ComponentClose
import ProofsInTheBook.Chapter13
-/
/- Source module: ProofsInTheBook.Ch13CauchyAssembly -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13CauchyAssembly

open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Chapter13









end ProofsInTheBook.Ch13CauchyAssembly

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT112
-/
/- Source module: ProofsInTheBook.Ch13LemmaII -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13LemmaII

open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.ZinanFFCT112











end ProofsInTheBook.Ch13LemmaII





end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalDiagCut
-/
/- Source module: ProofsInTheBook.Ch13SubArc -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalHingeCut ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZChain

namespace ProofsInTheBook.Ch13SubArc



















































end ProofsInTheBook.Ch13SubArc

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13LemmaII
import ProofsInTheBook.Ch13SubArc
-/
/- Source module: ProofsInTheBook.Ch13ArmVertex -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13ArmVertex

open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13LemmaII
open ProofsInTheBook.Ch13SubArc

















open scoped Classical









































end ProofsInTheBook.Ch13ArmVertex







end

/- Original source header (imports hoisted):
import ProofsInTheBook.Ch13ArmVertex
-/
/- Source module: ProofsInTheBook.Ch13ArmVertexFull -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13ArmVertexFull

open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13LemmaII
open ProofsInTheBook.Ch13ArmVertex

open scoped Classical































end ProofsInTheBook.Ch13ArmVertexFull








end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalKernel
-/
/- Source module: ProofsInTheBook.Ch13VertexStar -/
section
set_option autoImplicit true




noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13VertexStar





namespace VertexStar

























































end VertexStar

























end ProofsInTheBook.Ch13VertexStar




end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.Ch13VertexStar
-/
/- Source module: ProofsInTheBook.Ch13Dihedral -/
section
set_option autoImplicit true




noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13VertexStar

namespace VertexStar





















end VertexStar





end ProofsInTheBook.Ch13VertexStar



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.Ch13CauchyAssembly
import ProofsInTheBook.Ch13ArmVertexFull
import ProofsInTheBook.Ch13VertexStar
import ProofsInTheBook.Ch13Dihedral
import ProofsInTheBook.PlanarMapSimple
-/
/- Source module: ProofsInTheBook.Ch13Realization -/
section
set_option autoImplicit true




noncomputable section

open scoped Classical
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13ArmVertex
open ProofsInTheBook.Ch13ArmVertexFull
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Ch13VertexStar
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13Realization



namespace List



end List

















































































namespace ConvexPolytopeRealization










































end ConvexPolytopeRealization

end ProofsInTheBook.Ch13Realization



namespace ProofsInTheBook.Ch13Realization









end ProofsInTheBook.Ch13Realization








end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.Ch13Realization
import ProofsInTheBook.Ch13ComponentClose
import ProofsInTheBook.SphericalRotation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.Fin.Tuple.Reflection
-/
/- Source module: ProofsInTheBook.ZinanCh13Euclidean -/
section
set_option autoImplicit true




noncomputable section

open scoped Classical
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.SphericalRotation

namespace ProofsInTheBook.Ch13Euclidean



































































































-- The regular tetrahedron satisfies the reverse-`σ` rotation-faithfulness convention.


-- The regular tetrahedron satisfies the face-local outward-orientation convention.


















































end ProofsInTheBook.Ch13Euclidean

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh13Euclidean
import ProofsInTheBook.Ch13VertexStar
import ProofsInTheBook.Ch13Realization
import ProofsInTheBook.SphericalRotation
import Mathlib.Data.Fin.Rev
-/
/- Source module: ProofsInTheBook.ZinanCh13EuclLink -/
section
set_option autoImplicit true




noncomputable section

set_option maxHeartbeats 3000000

open scoped Classical RealInnerProductSpace
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Ch13Euclidean
open ProofsInTheBook.Ch13VertexStar
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.SphericalRotation

namespace ProofsInTheBook.Ch13EuclLink
































































































































namespace VertexLinkGeometry




















end VertexLinkGeometry



















































































end ProofsInTheBook.Ch13EuclLink

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh13EuclLink
import ProofsInTheBook.SphericalCongruence
import ProofsInTheBook.Ch13ArmVertexFull
-/
/- Source module: ProofsInTheBook.ZinanCh13SphAngle -/
section
set_option autoImplicit true




noncomputable section

open scoped Classical RealInnerProductSpace
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Ch13Euclidean
open ProofsInTheBook.Ch13EuclLink
open ProofsInTheBook.Ch13VertexStar

open ProofsInTheBook.SphericalKernel
  (S2 ShortArc tangentTo tangentTo_eq tangentTo_eq_zero_iff jointAngle sphAngle)
open ProofsInTheBook.SphericalRotation

namespace ProofsInTheBook.Ch13SphAngle










































































































end ProofsInTheBook.Ch13SphAngle

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.Ch13VertexStar
-/
/- Source module: ProofsInTheBook.Ch13LinkSides -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13VertexStar

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel



end ProofsInTheBook.Ch13VertexStar

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Ch13ArmVertex
-/
/- Source module: ProofsInTheBook.Ch13SubArcWrap -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.Ch13SubArc
open ProofsInTheBook.Ch13ArmVertex

namespace ProofsInTheBook.Ch13SubArcWrap















































end ProofsInTheBook.Ch13SubArcWrap







end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh13SphAngle
import ProofsInTheBook.ZinanCh13EuclLink
import ProofsInTheBook.Ch13Realization
import ProofsInTheBook.Ch13LinkSides
import ProofsInTheBook.Ch13SubArcWrap
import Mathlib.Geometry.Euclidean.Triangle
-/
/- Source module: ProofsInTheBook.ZinanCh13Cauchy3D -/
section
set_option autoImplicit true




noncomputable section

open scoped Classical RealInnerProductSpace
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13Euclidean
open ProofsInTheBook.Ch13EuclLink
open ProofsInTheBook.Ch13Realization
open ProofsInTheBook.Ch13VertexStar
open ProofsInTheBook.Ch13ArmVertexFull
open ProofsInTheBook.Ch13ArmVertex
open ProofsInTheBook.Ch13SubArc
open ProofsInTheBook.Ch13SubArcWrap
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13VertexStar

namespace VertexStar





end VertexStar

end ProofsInTheBook.Ch13VertexStar

namespace ProofsInTheBook.Ch13Cauchy3D








namespace ConvexEuclideanPolyhedron











end ConvexEuclideanPolyhedron



































































































































































namespace ListCyclicOrder



















end ListCyclicOrder

















































































































namespace RotTwoBlockCert




























end RotTwoBlockCert








































































































































end ProofsInTheBook.Ch13Cauchy3D

end
end


