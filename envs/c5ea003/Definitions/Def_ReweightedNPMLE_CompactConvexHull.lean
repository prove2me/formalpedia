-- Prove2me | Definitions.Def_ReweightedNPMLE_CompactConvexHull
-- name    : ReweightedNPMLE_CompactConvexHull
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:12:28.325227+00:00
-- url     : https://prove2.me/theorems/c00258fb-8d42-5f02-b56e-bcb7c559aa36
-- title:
--   Fixed-size barycentric representations and compact convex hulls
-- statement:
--   Let \(E\) be a finite-dimensional real normed space, with \(m=\dim_{\mathbb R}E\). Every point \(x\) in the convex hull of a nonempty set \(K\subseteq E\) admits a representation
--   \[
--   x=\sum_{j=1}^{m+1}w_jz_j,\qquad
--   w_j\ge0,\quad \sum_jw_j=1,\quad z_j\in K.
--   \]
--   Unused slots may carry zero weight and any fixed point of \(K\). The associated barycenter map sends the product of the standard simplex and \(K^{m+1}\) onto \(\operatorname{conv}(K)\). Therefore, when \(K\) is compact, its convex hull is compact without taking a closure. The compactness statement also includes the empty-set case.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/CompactConvexHull.lean#L22-L160

import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Fin.Embedding
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

/-!
# Compact convex hulls in finite dimension

Mathlib provides compactness of closed convex hulls and of convex hulls of
finite sets.  For the fitted-value problem we also need the classical
finite-dimensional fact that the convex hull of an arbitrary compact set is
itself compact.  We prove it by a fixed-cardinality Carathéodory
parameterization.
-/

open Set
open scoped BigOperators

namespace ReweightedNPMLE

/-- Carathéodory representations can be padded to exactly `finrank E + 1`
slots. -/
theorem exists_fixed_barycentric_representation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : K.Nonempty)
    {x : E} (hx : x ∈ convexHull ℝ K) :
    ∃ (w : Fin (Module.finrank ℝ E + 1) → ℝ)
      (z : Fin (Module.finrank ℝ E + 1) → E),
      w ∈ stdSimplex ℝ (Fin (Module.finrank ℝ E + 1)) ∧
      (∀ i, z i ∈ K) ∧ ∑ i, w i • z i = x := by
  classical
  obtain ⟨θ₀, hθ₀⟩ := hK
  obtain ⟨ι, hι, z, w, hzK, hzAff, hwpos, hwsum, hsum⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  letI : Fintype ι := hι
  have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 :=
    hzAff.card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le (vectorSpan ℝ (Set.range z))) 1)
  let e : ι ↪ Fin (Module.finrank ℝ E + 1) :=
    (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hcard)
  let R : Finset (Fin (Module.finrank ℝ E + 1)) := Finset.univ.image e
  let W : Fin (Module.finrank ℝ E + 1) → ℝ :=
    Function.extend e w (fun _ ↦ 0)
  let Z : Fin (Module.finrank ℝ E + 1) → E :=
    Function.extend e z (fun _ ↦ θ₀)
  have hW_apply (i : ι) : W (e i) = w i := by
    exact e.injective.extend_apply w (fun _ ↦ 0) i
  have hZ_apply (i : ι) : Z (e i) = z i := by
    exact e.injective.extend_apply z (fun _ ↦ θ₀) i
  have hW_zero (j : Fin (Module.finrank ℝ E + 1)) (hj : j ∉ R) : W j = 0 := by
    apply Function.extend_apply'
    intro hex
    rcases hex with ⟨i, hi⟩
    apply hj
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  have hsum_range : ∑ j ∈ R, W j = ∑ i : ι, w i := by
    symm
    apply Finset.sum_bij (fun i _ ↦ e i)
    · intro i _
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    · intro i _ j _ hij
      exact e.injective hij
    · intro j hj
      rcases Finset.mem_image.mp hj with ⟨i, _, rfl⟩
      exact ⟨i, Finset.mem_univ i, rfl⟩
    · intro i _
      exact (hW_apply i).symm
  have hWsum : ∑ j, W j = 1 := by
    calc
      (∑ j, W j) = ∑ j ∈ R, W j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ R)
        intro j _ hj
        exact hW_zero j hj
      _ = ∑ i : ι, w i := hsum_range
      _ = 1 := hwsum
  have hWnonneg (j : Fin (Module.finrank ℝ E + 1)) : 0 ≤ W j := by
    by_cases hj : j ∈ R
    · rcases Finset.mem_image.mp hj with ⟨i, _, rfl⟩
      rw [hW_apply]
      exact (hwpos i).le
    · rw [hW_zero j hj]
  have hZK (j : Fin (Module.finrank ℝ E + 1)) : Z j ∈ K := by
    by_cases hj : j ∈ R
    · rcases Finset.mem_image.mp hj with ⟨i, _, rfl⟩
      rw [hZ_apply]
      exact hzK (Set.mem_range_self i)
    · have hnot : ¬∃ i, e i = j := by
        intro hex
        rcases hex with ⟨i, hi⟩
        exact hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
      have hZj : Z j = θ₀ := by
        exact Function.extend_apply' z (fun _ ↦ θ₀) j hnot
      rw [hZj]
      exact hθ₀
  have hweighted_range : ∑ j ∈ R, W j • Z j = ∑ i : ι, w i • z i := by
    symm
    apply Finset.sum_bij (fun i _ ↦ e i)
    · intro i _
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    · intro i _ j _ hij
      exact e.injective hij
    · intro j hj
      rcases Finset.mem_image.mp hj with ⟨i, _, rfl⟩
      exact ⟨i, Finset.mem_univ i, rfl⟩
    · intro i _
      rw [hW_apply, hZ_apply]
  have hweighted : ∑ j, W j • Z j = x := by
    calc
      (∑ j, W j • Z j) = ∑ j ∈ R, W j • Z j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ R)
        intro j _ hj
        rw [hW_zero j hj, zero_smul]
      _ = ∑ i : ι, w i • z i := hweighted_range
      _ = x := hsum
  exact ⟨W, Z, ⟨hWnonneg, hWsum⟩, hZK, hweighted⟩

/-- In a finite-dimensional real normed space, the convex hull of a compact
set is compact (without taking a closure). -/
theorem isCompact_convexHull_of_isCompact_of_nonempty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E}
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty) :
    IsCompact (convexHull ℝ K) := by
  let I := Fin (Module.finrank ℝ E + 1)
  let D : Set ((I → ℝ) × (I → E)) :=
    stdSimplex ℝ I ×ˢ {z | ∀ i, z i ∈ K}
  let barycenter : ((I → ℝ) × (I → E)) → E :=
    fun wz ↦ ∑ i, wz.1 i • wz.2 i
  have hfunctions : IsCompact {z : I → E | ∀ i, z i ∈ K} :=
    isCompact_pi_infinite fun _ ↦ hKcompact
  have hDcompact : IsCompact D :=
    (isCompact_stdSimplex ℝ I).prod hfunctions
  have hbarycenter : Continuous barycenter := by
    unfold barycenter
    fun_prop
  have himage : IsCompact (barycenter '' D) := hDcompact.image hbarycenter
  have heq : convexHull ℝ K = barycenter '' D := by
    ext x
    constructor
    · intro hx
      obtain ⟨w, z, hw, hz, hsum⟩ :=
        exists_fixed_barycentric_representation hKnonempty hx
      exact ⟨(w, z), ⟨hw, hz⟩, hsum⟩
    · rintro ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
      apply mem_convexHull_of_exists_fintype w z hw.1 hw.2 hz
      rfl
  rw [heq]
  exact himage

theorem isCompact_convexHull_of_isCompact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hKcompact : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  rcases K.eq_empty_or_nonempty with hK | hK
  · rw [hK]
    simp
  · exact isCompact_convexHull_of_isCompact_of_nonempty hKcompact hK



end ReweightedNPMLE


