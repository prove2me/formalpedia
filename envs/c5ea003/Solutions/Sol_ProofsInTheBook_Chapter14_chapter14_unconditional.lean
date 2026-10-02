-- Prove2me | solution 1 for ProofsInTheBook.Chapter14.chapter14_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T16:10:12.512004+00:00
-- url     : https://prove2.me/submissions/2531d5b8-91cb-4069-9092-a8266239253b

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter14


/-!
# Chapter 14: Touching simplices

From *Proofs from THE BOOK*, Chapter 14:

* Bagemihl's conjecture predicts `f(d) = 2^d`.
* Perles's theorem, which is the upper-bound theorem actually proved in the
  chapter, states `f(d) < 2^(d+1)` for pairwise touching `d`-simplices.
  This is the statement printed as Theorem 2 in the local Springer PDF; the
  sharper `≤ 2^d` is the conjectural sharp value discussed just before the
  lower-bound construction, not the Perles bound proved by the book.

The old formalization only proved a pigeonhole statement from an already
injective map into `Fin d → Bool`.  That is not the Chapter 14 argument.  This
file now records the geometric objects and proves the Perles B/C-matrix
counting step.  It also proves the local simplex-side geometry available in
Mathlib: a simplex's closed body is weakly on the same side of each facet as
the opposite vertex, and its relative interior is strictly on that side.
The remaining unformalized frontier is the extraction of the certified Perles
matrix from a raw family of touching simplices; see
`PerlesFacetSeparationData` below for the exact missing fields:

* enumerate the distinct oriented facet hyperplanes of the configuration;
  this file now constructs the finite type of distinct unoriented affine facet
  hyperplanes, proves the no-accidental-containment/dimension lemma, and proves
  the exact `d+1` row-incidence count for `HasFacetIn`;
* package affine facet hyperplanes as oriented halfspaces compatible with the
  Mathlib `WSameSide`/`SSameSide` facts proved below; this file now orients
  each distinct hyperplane by a chosen incident simplex facet and proves every
  incident simplex lies in one of the two closed signed-distance sides.  Hence
  `PerlesFacetSeparationData.ofFacetHyperplanes` now fills the B-row zero count
  without a side-completeness hypothesis;
* prove a touching pair has opposite signs in some shared facet hyperplane from
  the raw touching relation; `TouchesAcrossFacets` isolates the exact
  opposite-vertex `SOppSide` condition and proves it implies
  `TouchesAlongFacets`, and
  `exists_orientedHyperplane_opposite_entries_of_touchesAcrossFacets` proves
  the local signed-distance opposite B-entries under that condition.  This file
  now also transfers those opposite entries to the globally chosen
  `FacetHyperplanes.oriented` representative, and
  `chapter14_of_pairwiseTouchingAcrossFacets` proves the Perles bound directly
  from this stronger geometric relation.  This file now also proves the
  same-side obstruction impossible for the strengthened relation
  `TouchesAlongFacetInteriors`: if the two facet relative interiors overlap
  and the opposite vertices are on the same side, a small barycentric move from
  the overlap point produces a common full relative-interior point.  Thus
  `chapter14_of_pairwiseTouchingAlongFacetInteriors` constructs the Perles
  data without `PairwiseNoSameSideCommonFacet`.  The remaining semantic gap is
  deriving this facet-interior touching data from the raw book touching
  relation, whose boundary-contact formulation is not yet formalized here;
* construct a point outside all simplex bodies to obtain the missing completed
  sign vector.  The halfspace side of this step is now formalized for one
  simplex:
  `DSimplex.mem_body_iff_forall_signedInfDist_nonneg` proves that the closed
  simplex is exactly the intersection of its closed signed facet halfspaces;
  `DSimplex.exists_signedInfDist_neg_of_notMem_body` gives the violated facet
  for a point outside one simplex.  This file now also proves both that a point
  outside every body yields the missing sign vector and that such a point
  exists for every finite positive-dimensional family.

Why this file does not claim `Fintype.card ι ≤ 2^d`: the current B/C-matrix
data only proves that the completed rows form a proper subset of the `2^s` sign
vectors.  That gives
`2^(s-d-1) * r < 2^s`, hence `r < 2^(d+1)`.  Removing the remaining factor of
two would require an additional half-cube invariant, for example that completed
rows contain at most one vector from each antipodal pair, or equivalently that
one sign coordinate/parity is determined by the rest.  Such an invariant is not
part of `PerlesFacetSeparationData` and is not proved from the current abstract
matrix fields.  The gap to `≤ 2^d`, if one wants to pursue the conjectural
sharp bound rather than the book's Perles theorem, is exactly this extra
geometric half-cube argument.

This file does formalize the sharpened combinatorial endpoint under one such
extra half-cube invariant: if all completed sign vectors have a fixed value in
one coordinate, then the completed rows inject into a half-cube and
`Fintype.card ι ≤ 2^d`; see `PerlesMatrix.card_le_two_pow_of_fixedCoordinate`
and `chapter14_sharp_of_fixedCoordinate`.  It also proves the more natural
antipodal-free half-cube endpoint; see
`PerlesMatrix.card_le_two_pow_of_antipodalFree` and
`chapter14_sharp_of_antipodalFree`.  The data-free wrappers
`chapter14_sharp_of_pairwiseTouchingAcrossFacets_fixedCoordinate`,
`chapter14_sharp_of_pairwiseTouchingAcrossFacets_antipodalFree`, the
`TouchesAlongFacetInteriors` wrappers, and the
`PairwiseNoSameSideCommonFacet` analogues apply these endpoints to canonical
matrices extracted in this file.  The remaining gap is geometric: derive that
fixed-coordinate/parity/antipodal-free invariant, or an equivalent half-cube
bound, from raw touching simplices.
-/

noncomputable section

namespace ProofsInTheBook.Chapter14

open scoped Classical Topology

/-! ## Geometric setup -/



















/-- The closed opposite facet lies in the closed simplex body. -/
lemma DSimplex.faceOpposite_closedInterior_subset_body {d : ℕ} [NeZero d]
    (S : DSimplex d) (i : Fin (d + 1)) :
    (S.faceOpposite i).closedInterior ⊆ S.body :=
  S.closedInterior_faceOpposite_subset_closedInterior i

/-- The relative interior of an opposite facet lies in the closed simplex body. -/
lemma DSimplex.faceOpposite_interior_subset_body {d : ℕ} [NeZero d]
    (S : DSimplex d) (i : Fin (d + 1)) :
    (S.faceOpposite i).interior ⊆ S.body :=
  (S.faceOpposite i).interior_subset_closedInterior.trans
    (S.faceOpposite_closedInterior_subset_body i)











/--
Barycentric coordinates of a point in the relative interior of the facet
opposite `i`: the missing coordinate is zero, and all other coordinates are
strictly positive.
-/
lemma DSimplex.affineBasis_coord_faceOpposite_interior {d : ℕ} [NeZero d]
    (S : DSimplex d) (i : Fin (d + 1)) {p : Ambient d}
    (hp : p ∈ (S.faceOpposite i).interior) :
    (∀ k : Fin (d + 1), k ≠ i → 0 < (S.affineBasis).coord k p) ∧
      (S.affineBasis).coord i p = 0 := by
  classical
  let B := S.affineBasis
  have hsum : ∑ k, B.coord k p = 1 := AffineBasis.sum_coord_apply_eq_one B p
  have hp_eq : (Finset.univ.affineCombination ℝ S.points fun k => B.coord k p) = p := by
    change (Finset.univ.affineCombination ℝ B fun k => B.coord k p) = p
    exact AffineBasis.affineCombination_coord_eq_self B p
  have hp_face : (Finset.univ.affineCombination ℝ S.points fun k => B.coord k p) ∈
      (S.faceOpposite i).interior := by
    simpa [hp_eq] using hp
  rw [Affine.Simplex.faceOpposite] at hp_face
  have hcoords := (S.affineCombination_mem_interior_face_iff_mem_Ioo
    (fs := ({i}ᶜ : Finset (Fin (d + 1))))
    (m := d - 1) (by simp [Finset.card_compl, NeZero.one_le]) hsum).1 hp_face
  constructor
  · intro k hk
    exact (hcoords.1 k (by simpa using hk)).1
  · exact hcoords.2 i (by simp)

















































/-- Same-side position is exactly positive barycentric coordinate at the opposite vertex. -/
lemma DSimplex.affineBasis_coord_pos_of_vertices_sSameSide {d : ℕ} [NeZero d]
    (S : DSimplex d) (i : Fin (d + 1)) {p : Ambient d}
    (hsame : (S.facetHyperplane i).SSameSide (S.points i) p) :
    0 < (S.affineBasis).coord i p := by
  let B := S.affineBasis
  have hsigned : 0 < S.signedInfDist i p :=
    S.signedInfDist_pos_of_vertices_sSameSide i hsame
  have hmul : 0 < B.coord i p *
      ‖S.points i -ᵥ ↑((S.faceOpposite i).orthogonalProjectionSpan (S.points i))‖ := by
    simpa [S.signedInfDist_eq_affineBasis_coord_mul_norm i p, B] using hsigned
  exact pos_of_mul_pos_left hmul (norm_nonneg _)



























/--
Every point of a simplex's relative interior is strictly on the same side of a
facet hyperplane as the opposite vertex.
-/
lemma DSimplex.relInterior_sSameSide_opposite_vertex {d : ℕ} [NeZero d]
    (S : DSimplex d) (i : Fin (d + 1)) {p : Ambient d} (hp : p ∈ S.relInterior) :
    (S.facetHyperplane i).SSameSide p (S.points i) := by
  rw [DSimplex.relInterior] at hp
  rcases hp with ⟨w, hw, hw01, rfl⟩
  rw [DSimplex.facetHyperplane]
  exact (S.sSameSide_affineSpan_faceOpposite_point_right_iff hw).2 (hw01 i).1

/--
If two simplices have a common facet hyperplane and the two opposite vertices
are strictly on opposite sides of it, then all relative-interior points are
strictly on opposite sides.  This is the formal local side-composition lemma
needed for the geometric `pairwiseOpposite` field.
-/
lemma DSimplex.relInterior_sOppSide_of_commonFacet_of_vertices_sOppSide {d : ℕ}
    [NeZero d] (S T : DSimplex d) (i j : Fin (d + 1))
    {p q : Ambient d} (hp : p ∈ S.relInterior) (hq : q ∈ T.relInterior)
    (hfacet : S.facetHyperplane i = T.facetHyperplane j)
    (hopposite : (S.facetHyperplane i).SOppSide (S.points i) (T.points j)) :
    (S.facetHyperplane i).SOppSide p q := by
  have hp_side := S.relInterior_sSameSide_opposite_vertex i hp
  have hq_side : (S.facetHyperplane i).SSameSide (T.points j) q := by
    simpa [hfacet] using (T.relInterior_sSameSide_opposite_vertex j hq).symm
  exact (hp_side.trans_sOppSide hopposite).trans_sSameSide hq_side















/-- Overlapping facet interiors give a point in the intersection of the closed bodies. -/
lemma facetInteriorOverlap_body_inter_nonempty {d : ℕ} [NeZero d]
    {S T : DSimplex d} {i j : Fin (d + 1)}
    (h : FacetInteriorOverlap S T i j) :
    (S.body ∩ T.body).Nonempty := by
  rcases h with ⟨p, hpS, hpT⟩
  exact ⟨p, S.faceOpposite_interior_subset_body i hpS,
    T.faceOpposite_interior_subset_body j hpT⟩

/-- Positive barycentric weights summing to one are strictly between zero and one. -/
lemma fin_weight_mem_Ioo_of_pos_of_sum_eq_one {d : ℕ} [NeZero d]
    {w : Fin (d + 1) → ℝ} (hpos : ∀ k, 0 < w k) (hsum : ∑ k, w k = 1)
    (k : Fin (d + 1)) :
    w k ∈ Set.Ioo (0 : ℝ) 1 := by
  refine ⟨hpos k, ?_⟩
  obtain ⟨l, hlk⟩ := exists_ne k
  have hlt : w k < ∑ x ∈ Finset.univ, w x := by
    exact Finset.single_lt_sum hlk (Finset.mem_univ k) (Finset.mem_univ l) (hpos l)
      (fun x _ hx => (hpos x).le)
  simpa [hsum] using hlt

/--
For finitely many positive coordinates `a k`, a sufficiently small positive
line-map parameter keeps all interpolated coordinates
`(1 - δ) * a k + δ * b k` positive.
-/
lemma exists_pos_lt_one_forall_lineMap_pos {α : Type*} [Fintype α]
    (a b : α → ℝ) (ha : ∀ k, 0 < a k) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ k, 0 < (1 - δ) * a k + δ * b k := by
  classical
  have hpos : ∀ k : α, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      0 < (1 - δ) * a k + δ * b k := by
    intro k
    have hcont : ContinuousAt (fun δ : ℝ => (1 - δ) * a k + δ * b k) 0 := by
      fun_prop
    have hlim : Filter.Tendsto (fun δ : ℝ => (1 - δ) * a k + δ * b k)
        (𝓝[>] (0 : ℝ)) (𝓝 (a k)) := by
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    exact hlim.eventually (isOpen_Ioi.mem_nhds (ha k))
  have hall : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∀ k : α, 0 < (1 - δ) * a k + δ * b k := by
    simpa using (Filter.eventually_all_finite
      (Set.finite_univ : (Set.univ : Set α).Finite)).mpr (fun k _ => hpos k)
  have hδpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  have hδlt : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 := by
    exact eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)
  rcases (hall.and hδpos |>.and hδlt).exists with ⟨δ, hδall, hδlt⟩
  exact ⟨δ, hδall.2, hδlt, hδall.1⟩

/--
If two facet interiors overlap and the opposite vertices are strictly on the
same side of the first facet hyperplane, then the two full simplex relative
interiors intersect.  Algebraically, move a sufficiently small distance from
the common facet-interior point toward `T`'s opposite vertex.
-/
lemma facetInteriorOverlap_relInterior_inter_nonempty_of_vertices_sSameSide
    {d : ℕ} [NeZero d] {S T : DSimplex d} {i j : Fin (d + 1)}
    (hoverlap : FacetInteriorOverlap S T i j)
    (hsame : (S.facetHyperplane i).SSameSide (S.points i) (T.points j)) :
    (S.relInterior ∩ T.relInterior).Nonempty := by
  classical
  rcases hoverlap with ⟨p, hpS, hpT⟩
  let BS := S.affineBasis
  let BT := T.affineBasis
  have hSface := S.affineBasis_coord_faceOpposite_interior i hpS
  have hTface := T.affineBasis_coord_faceOpposite_interior j hpT
  have hSi0 : BS.coord i p = 0 := by simpa [BS] using hSface.2
  have hTj0 : BT.coord j p = 0 := by simpa [BT] using hTface.2
  have hTiS : 0 < BS.coord i (T.points j) := by
    simpa [BS] using S.affineBasis_coord_pos_of_vertices_sSameSide i hsame
  let a : {k : Fin (d + 1) // k ≠ i} → ℝ := fun k => BS.coord k.1 p
  let b : {k : Fin (d + 1) // k ≠ i} → ℝ := fun k => BS.coord k.1 (T.points j)
  have ha : ∀ k, 0 < a k := by
    intro k
    exact hSface.1 k.1 k.2
  rcases exists_pos_lt_one_forall_lineMap_pos a b ha with
    ⟨δ, hδpos, hδlt, hδSrest⟩
  let q : Ambient d := AffineMap.lineMap p (T.points j) δ
  refine ⟨q, ?_, ?_⟩
  · let wS : Fin (d + 1) → ℝ := AffineMap.lineMap (fun k => BS.coord k p)
      (fun k => BS.coord k (T.points j)) δ
    have hsumS : ∑ k, wS k = 1 := by
      simp [wS, AffineMap.lineMap_apply_module, Finset.sum_add_distrib, ← Finset.mul_sum,
        AffineBasis.sum_coord_apply_eq_one]
    have hp_eqS : (Finset.univ.affineCombination ℝ S.points fun k => BS.coord k p) = p := by
      change (Finset.univ.affineCombination ℝ BS fun k => BS.coord k p) = p
      exact AffineBasis.affineCombination_coord_eq_self BS p
    have hTj_eqS :
        (Finset.univ.affineCombination ℝ S.points fun k => BS.coord k (T.points j)) =
          T.points j := by
      change (Finset.univ.affineCombination ℝ BS fun k => BS.coord k (T.points j)) =
        T.points j
      exact AffineBasis.affineCombination_coord_eq_self BS (T.points j)
    have hqS : q = Finset.univ.affineCombination ℝ S.points wS := by
      calc
        q = AffineMap.lineMap
            (Finset.univ.affineCombination ℝ S.points fun k => BS.coord k p)
            (Finset.univ.affineCombination ℝ S.points fun k => BS.coord k (T.points j)) δ := by
          rw [hp_eqS, hTj_eqS]
        _ = Finset.univ.affineCombination ℝ S.points wS := by
          rw [Finset.lineMap_affineCombination]
    rw [DSimplex.relInterior, hqS]
    exact (Affine.Simplex.affineCombination_mem_interior_iff (s := S) hsumS).2 (fun k =>
      fin_weight_mem_Ioo_of_pos_of_sum_eq_one (d := d) (w := wS) (by
        intro l
        by_cases hli : l = i
        · subst l
          have hw : wS i = δ * BS.coord i (T.points j) := by
            simp [wS, AffineMap.lineMap_apply_module, hSi0]
          rw [hw]
          exact mul_pos hδpos hTiS
        · have hw : wS l = (1 - δ) * BS.coord l p + δ * BS.coord l (T.points j) := by
            simp [wS, AffineMap.lineMap_apply_module]
          rw [hw]
          exact hδSrest ⟨l, hli⟩) hsumS k)
  · let wT : Fin (d + 1) → ℝ := AffineMap.lineMap (fun k => BT.coord k p)
      (Pi.single j (1 : ℝ)) δ
    have hsumT : ∑ k, wT k = 1 := by
      simp [wT, AffineMap.lineMap_apply_module, Finset.sum_add_distrib, ← Finset.mul_sum,
        AffineBasis.sum_coord_apply_eq_one]
    have hp_eqT : (Finset.univ.affineCombination ℝ T.points fun k => BT.coord k p) = p := by
      change (Finset.univ.affineCombination ℝ BT fun k => BT.coord k p) = p
      exact AffineBasis.affineCombination_coord_eq_self BT p
    have hTj_eqT :
        (Finset.univ.affineCombination ℝ T.points (Pi.single j (1 : ℝ))) = T.points j := by
      exact Finset.univ.affineCombination_piSingle ℝ T.points (Finset.mem_univ j)
    have hqT : q = Finset.univ.affineCombination ℝ T.points wT := by
      calc
        q = AffineMap.lineMap
            (Finset.univ.affineCombination ℝ T.points fun k => BT.coord k p)
            (Finset.univ.affineCombination ℝ T.points (Pi.single j (1 : ℝ))) δ := by
          rw [hp_eqT, hTj_eqT]
        _ = Finset.univ.affineCombination ℝ T.points wT := by
          rw [Finset.lineMap_affineCombination]
    rw [DSimplex.relInterior, hqT]
    exact (Affine.Simplex.affineCombination_mem_interior_iff (s := T) hsumT).2 (fun k =>
      fin_weight_mem_Ioo_of_pos_of_sum_eq_one (d := d) (w := wT) (by
        intro l
        by_cases hlj : l = j
        · subst l
          have hw : wT j = δ := by
            simp [wT, AffineMap.lineMap_apply_module, hTj0]
          rw [hw]
          exact hδpos
        · have hw : wT l = (1 - δ) * BT.coord l p := by
            simp [wT, AffineMap.lineMap_apply_module, hlj]
          rw [hw]
          exact mul_pos (sub_pos.mpr hδlt) (hTface.1 l hlj)) hsumT k)

/--
If two specified facet interiors overlap while the full simplex relative
interiors are disjoint, then the opposite vertices cannot lie on the same
strict side of the common facet hyperplane.  This packages the local geometric
obstruction discharged by the barycentric construction above.
-/
lemma not_sSameSide_of_facetInteriorOverlap_of_disjoint_relInterior
    {d : ℕ} [NeZero d] {S T : DSimplex d} {i j : Fin (d + 1)}
    (hdisj : Disjoint S.relInterior T.relInterior)
    (hoverlap : FacetInteriorOverlap S T i j) :
    ¬ (S.facetHyperplane i).SSameSide (S.points i) (T.points j) := by
  intro hsame
  rcases facetInteriorOverlap_relInterior_inter_nonempty_of_vertices_sSameSide
    hoverlap hsame with ⟨p, hpS, hpT⟩
  exact Set.disjoint_left.mp hdisj hpS hpT







/--
Facet-interior touching supplies a specified common facet for which the
same-side alternative is impossible.
-/
lemma touchesAlongFacetInteriors_exists_not_sSameSide {d : ℕ} [NeZero d]
    {S T : DSimplex d} (h : TouchesAlongFacetInteriors S T) :
    ∃ i j, S.facetHyperplane i = T.facetHyperplane j ∧
      FacetInteriorOverlap S T i j ∧
        ¬ (S.facetHyperplane i).SSameSide (S.points i) (T.points j) := by
  rcases h with ⟨hdisj, i, j, hfacet, hoverlap⟩
  exact ⟨i, j, hfacet, hoverlap,
    not_sSameSide_of_facetInteriorOverlap_of_disjoint_relInterior hdisj hoverlap⟩



/--
Facet-interior touching rules out the same-side alternative: if the opposite
vertices were on the same side, the local barycentric construction above would
produce a common relative-interior point.
-/
lemma touchesAcrossFacets_of_touchesAlongFacetInteriors {d : ℕ} [NeZero d]
    {S T : DSimplex d} (h : TouchesAlongFacetInteriors S T) :
    TouchesAcrossFacets S T := by
  rcases touchesAlongFacetInteriors_exists_not_sSameSide h with
    ⟨i, j, hfacet, hoverlap, hnotSame⟩
  have hnot : T.points j ∉ S.facetHyperplane i := by
    intro hmem
    exact T.opposite_vertex_notMem_facetHyperplane j (by simpa [hfacet] using hmem)
  rcases S.sSameSide_or_sOppSide_opposite_vertex_of_notMem_facetHyperplane i hnot with
    hsame | hopp
  · exact False.elim (hnotSame hsame)
  · exact ⟨facetInteriorOverlap_body_inter_nonempty hoverlap, i, j, hfacet, hopp⟩





/--
The opposite-vertex side condition is strong enough to imply disjoint relative
interiors, hence the weaker `TouchesAlongFacets` relation.
-/
lemma touchesAlongFacets_of_touchesAcrossFacets {d : ℕ} [NeZero d]
    {S T : DSimplex d} (h : TouchesAcrossFacets S T) :
    TouchesAlongFacets S T := by
  rcases h with ⟨hmeet, i, j, hfacet, hopposite⟩
  refine ⟨?_, hmeet, ⟨i, j, hfacet⟩⟩
  rw [Set.disjoint_left]
  intro p hpS hpT
  exact AffineSubspace.not_sOppSide_self (S.facetHyperplane i) p
    (S.relInterior_sOppSide_of_commonFacet_of_vertices_sOppSide T i j hpS hpT hfacet hopposite)



















lemma pairwiseTouching_of_pairwiseTouchingAcrossFacets {ι : Type*} {d : ℕ}
    [NeZero d] {simplices : ι → DSimplex d}
    (h : PairwiseTouchingAcrossFacets simplices) :
    PairwiseTouching simplices := by
  intro i j hij
  exact touchesAlongFacets_of_touchesAcrossFacets (h hij)



/-- Facet-interior touching gives the across-facet certificates directly. -/
lemma pairwiseTouchingAcrossFacets_of_pairwiseTouchingAlongFacetInteriors
    {ι : Type*} {d : ℕ} [NeZero d] {simplices : ι → DSimplex d}
    (h : PairwiseTouchingAlongFacetInteriors simplices) :
    PairwiseTouchingAcrossFacets simplices := by
  intro i j hij
  exact touchesAcrossFacets_of_touchesAlongFacetInteriors (h hij)























set_option synthInstance.maxHeartbeats 80000





namespace OrientedHyperplane















































end OrientedHyperplane



namespace FacetHyperplanes

variable {ι : Type*} {d : ℕ} [NeZero d] (simplices : ι → DSimplex d)







































end FacetHyperplanes

/-! ## Perles B/C-matrix core -/



namespace FacetHyperplanes

variable {ι : Type*} {d : ℕ} [NeZero d] (simplices : ι → DSimplex d)





end FacetHyperplanes



namespace PerlesMatrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}







lemma completedSign_of_some (M : PerlesMatrix ι κ d) {i : ι}
    (z : M.ZeroPos i → Bool) {j : κ} {b : Bool} (h : M.entry i j = some b) :
    M.completedSign ⟨i, z⟩ j = b := by
  simp [completedSign, h]

lemma completedSign_of_none (M : PerlesMatrix ι κ d) {i : ι}
    (z : M.ZeroPos i → Bool) {j : κ} (h : M.entry i j = none) :
    M.completedSign ⟨i, z⟩ j = z ⟨j, h⟩ := by
  simp [completedSign, h]

lemma completedSign_extends (M : PerlesMatrix ι κ d) (x : M.CompletionIndex) :
    EntryExtends (M.entry x.1) (M.completedSign x) := by
  intro j b hb
  exact M.completedSign_of_some x.2 hb

lemma completedSign_injective (M : PerlesMatrix ι κ d) :
    Function.Injective M.completedSign := by
  rintro ⟨i, zi⟩ ⟨j, zj⟩ h
  by_cases hij : i = j
  · subst j
    congr
    funext z
    have hz := congrFun h z.1
    rw [M.completedSign_of_none zi z.2, M.completedSign_of_none zj z.2] at hz
    exact hz
  · rcases M.pairwiseOpposite hij with ⟨c, b, hic, hjc⟩
    have hc := congrFun h c
    have hi : M.completedSign ⟨i, zi⟩ c = b := by
      exact M.completedSign_of_some zi hic
    have hj : M.completedSign ⟨j, zj⟩ c = !b := by
      exact M.completedSign_of_some zj hjc
    rw [hi, hj] at hc
    cases b <;> simp at hc

lemma completedSign_not_surjective (M : PerlesMatrix ι κ d) :
    ¬ Function.Surjective M.completedSign := by
  rintro hsurj
  rcases M.missingSignVector with ⟨v, hv⟩
  rcases hsurj v with ⟨x, rfl⟩
  exact hv x.1 (M.completedSign_extends x)

lemma card_zeroPos (M : PerlesMatrix ι κ d) (i : ι) :
    Fintype.card (M.ZeroPos i) = Fintype.card κ - (d + 1) := by
  classical
  change Fintype.card {j : κ // M.entry i j = none} = Fintype.card κ - (d + 1)
  rw [Fintype.card_subtype]
  exact M.rowZeroCard i

lemma card_completionIndex (M : PerlesMatrix ι κ d) :
    Fintype.card M.CompletionIndex =
      Fintype.card ι * 2 ^ (Fintype.card κ - (d + 1)) := by
  classical
  simp [CompletionIndex, card_zeroPos, Fintype.card_sigma, Finset.sum_const,
    Finset.card_univ]

/-- The C-matrix has fewer rows than all possible sign vectors of length `s`. -/
theorem scaled_bound (M : PerlesMatrix ι κ d) :
    Fintype.card ι * 2 ^ (Fintype.card κ - (d + 1)) < 2 ^ Fintype.card κ := by
  classical
  have hlt := Fintype.card_lt_of_injective_not_surjective M.completedSign
    M.completedSign_injective M.completedSign_not_surjective
  rw [M.card_completionIndex] at hlt
  simpa using hlt

/-- Perles's B/C-matrix counting conclusion. -/
theorem card_lt_two_pow_succ (M : PerlesMatrix ι κ d) :
    Fintype.card ι < 2 ^ (d + 1) := by
  classical
  have hscaled := M.scaled_bound
  have hpow :
      2 ^ Fintype.card κ =
        2 ^ (d + 1) * 2 ^ (Fintype.card κ - (d + 1)) := by
    rw [← pow_add, Nat.add_sub_of_le M.dimension_le_columns]
  rw [hpow] at hscaled
  exact Nat.lt_of_mul_lt_mul_right hscaled





























end PerlesMatrix

/-! ## Certified geometric data for Chapter 14 -/



namespace PerlesFacetSeparationData

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ} [NeZero d]
    {simplices : ι → DSimplex d}



















variable [Nonempty ι]













end PerlesFacetSeparationData

/--
Chapter 14, as currently formalized: Perles's upper bound follows from a raw
pairwise touching family once the facet-hyperplane sign data have been
extracted and certified.

This deliberately no longer accepts an arbitrary injective sign map.  The
remaining missing theorem is the geometric construction of
`PerlesFacetSeparationData` from `PairwiseTouching simplices`.
-/
theorem chapter14 {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ} [NeZero d]
    (simplices : ι → DSimplex d) (htouch : PairwiseTouching simplices)
    (data : PerlesFacetSeparationData simplices κ) :
    Fintype.card ι < 2 ^ (d + 1) :=
  (data.toPerlesMatrix htouch).card_lt_two_pow_succ

/--
Chapter 14 with the current strongest formal geometric input: if each touching
pair is certified to touch across a common facet with opposite vertices on
opposite strict sides, then the Perles bound follows with no separate
facet-separation data hypothesis.

The remaining semantic gap to the raw book statement is exactly the extraction
of `PairwiseTouchingAcrossFacets` from the intended raw touching definition.
-/
theorem chapter14_of_pairwiseTouchingAcrossFacets {ι : Type*} [Fintype ι]
    {d : ℕ} [NeZero d] (simplices : ι → DSimplex d)
    (hacross : PairwiseTouchingAcrossFacets simplices) :
    Fintype.card ι < 2 ^ (d + 1) := by
  classical
  by_cases hι : Nonempty ι
  · letI := hι
    exact chapter14 simplices (pairwiseTouching_of_pairwiseTouchingAcrossFacets hacross)
      (PerlesFacetSeparationData.ofFacetHyperplanesAcross simplices hacross)
  · haveI : IsEmpty ι := ⟨fun x => hι ⟨x⟩⟩
    simp

/--
Chapter 14 from the stronger facet-interior touching relation.  The same-side
common-facet obstruction is now proved impossible for this relation, so the
across-facet Perles data are constructed directly from the geometry.
-/
theorem chapter14_of_pairwiseTouchingAlongFacetInteriors {ι : Type*} [Fintype ι]
    {d : ℕ} [NeZero d] (simplices : ι → DSimplex d)
    (htouch : PairwiseTouchingAlongFacetInteriors simplices) :
    Fintype.card ι < 2 ^ (d + 1) :=
  chapter14_of_pairwiseTouchingAcrossFacets simplices
    (pairwiseTouchingAcrossFacets_of_pairwiseTouchingAlongFacetInteriors htouch)































end ProofsInTheBook.Chapter14

open ProofsInTheBook.Chapter14
open scoped Classical Topology
set_option synthInstance.maxHeartbeats 80000

theorem solution {ι : Type*} [Fintype ι]
    {d : ℕ} [NeZero d] (simplices : ι → DSimplex d)
    (htouch : FaithfulPairwiseTouching simplices) :
    Fintype.card ι < 2 ^ (d + 1) :=
  chapter14_of_pairwiseTouchingAlongFacetInteriors simplices htouch
