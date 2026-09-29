-- Prove2me | Definitions.Def_erdos183_core
-- name    : erdos183_core
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-04T00:14:50.988927+00:00
-- url     : https://prove2.me/theorems/6b101e3f-ba2a-4797-aef5-42b73b3b46fb
-- title:
--   Multicolour triangle Ramsey numbers and the palette-block construction
-- statement:
--   This bundle collects the definitions underlying the resolution of Erdős problem 183 on multicolour triangle Ramsey numbers.
--
--   The basic objects are the following. A $k$-edge-colouring $C$ of a graph on vertex set $V$ is *triangle-free* (`TriangleFree`) when no colour class contains a triangle, i.e. each graph $C^{-1}(\text{colour})$ is $K_3$-free. We say $n$ *forces a monochromatic triangle* for $k$ colours (`ForcesMonochromaticTriangle n k`) when no $k$-colouring of the edges of $K_n$ is triangle-free. The $k$-colour triangle Ramsey number is then
--
--   $$R_k \;=\; \inf\{\, n \in \mathbb{N} \;:\; n \text{ forces a monochromatic triangle for } k \text{ colours} \,\}.$$
--
--   The remaining definitions support the lower-bound construction, which builds large triangle-free colourings by recursion on a *palette* structure. A `PaletteBlockCertificate` packages the data certifying that a block of a colouring can be recoloured without creating a monochromatic triangle: a palette $\text{palette}(i)$ of colours attached to each index $i$, a labelling of the vertices by $\mathrm{Fin}\,j$ for colours outside that palette, and the hypotheses that internal edges carry no triangle and that crossing edges change palette membership. From such certificates one assembles the global colouring `globalLabel` and derives colourability of the associated graphs.
--
--   The quantitative parameters `paletteLogWidth`, `saturatedMatrixWidth`, `saturatedMatrixRows` and `paletteColourCount` track the growth of the construction across stages, and `PaletteGrowthBound` records the inequality relating the number of vertices produced at a stage to those parameters. These are the quantities that turn the recursion into the explicit bound on $R_k$.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean source https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L8-L2245

import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

open Filter Finset SimpleGraph
open scoped Topology

namespace Erdos183

def TriangleFree {n k : ℕ}
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) : Prop :=
  ∀ colour : Fin k, (C.labelGraph colour).CliqueFree 3

noncomputable def omittedColourEquiv (k : ℕ) (omitted : Fin (k + 1)) :
    {colour : Fin (k + 1) // colour ≠ omitted} ≃ Fin k := by
  classical
  apply Fintype.equivFinOfCardEq
  rw [Fintype.card_subtype_compl (fun colour : Fin (k + 1) =>
    colour = omitted)]
  simp

noncomputable def activeColourEquiv (N t : ℕ) (P : Finset (Fin N))
    (hP : P.card = t) :
    Fin (N - t) ≃ {colour : Fin N // colour ∉ P} := by
  classical
  refine (Fintype.equivFinOfCardEq ?_).symm
  rw [Fintype.card_subtype_compl (fun colour : Fin N => colour ∈ P)]
  simp [Fintype.card_subtype, hP]

noncomputable def activeColourPreimage (N t : ℕ) (P : Finset (Fin N))
    (hP : P.card = t) (colour : Fin N) (hactive : colour ∉ P) :
    Fin (N - t) :=
  (activeColourEquiv N t P hP).symm ⟨colour, hactive⟩

noncomputable def paletteRelabel {V : Type*} {N t : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (P : Finset (Fin N)) (hP : P.card = t) :
    SimpleGraph.TopEdgeLabeling V (Fin N) :=
  C.compRight (fun colour => (activeColourEquiv N t P hP colour).val)

theorem paletteRelabel_adj_iff {V : Type*} {N t : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (P : Finset (Fin N)) (hP : P.card = t)
    (colour : Fin N) (hactive : colour ∉ P) (u v : V) :
    ((paletteRelabel C P hP).labelGraph colour).Adj u v ↔
      (C.labelGraph (activeColourPreimage N t P hP colour hactive)).Adj u v := by
  constructor
  · intro hadj
    obtain ⟨hne, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mp hadj
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mpr
    refine ⟨hne, ?_⟩
    apply (activeColourEquiv N t P hP).injective
    apply Subtype.ext
    simpa [paletteRelabel, activeColourPreimage] using hcolour
  · intro hadj
    obtain ⟨hne, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mp hadj
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mpr
    refine ⟨hne, ?_⟩
    change (activeColourEquiv N t P hP (C.get u v hne)).val = colour
    have heq := congrArg
      (fun old => (activeColourEquiv N t P hP old).val) hcolour
    simpa [activeColourPreimage] using heq

theorem paletteRelabel_missing_no_adj {V : Type*} {N t : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (P : Finset (Fin N)) (hP : P.card = t)
    (colour : Fin N) (hmissing : colour ∈ P) (u v : V) :
    ¬ ((paletteRelabel C P hP).labelGraph colour).Adj u v := by
  intro hadj
  obtain ⟨hne, hcolour⟩ :=
    (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mp hadj
  have hnot : (paletteRelabel C P hP).get u v hne ∉ P :=
    (activeColourEquiv N t P hP (C.get u v hne)).property
  rw [hcolour] at hnot
  exact hnot hmissing

noncomputable def paletteBlockLabel {V : Type*} {N t j : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (P : Finset (Fin N)) (hP : P.card = t)
    (colour : Fin N) (hactive : colour ∉ P) : V → Fin j :=
  fun v =>
    (Classical.choice
      (hC (activeColourPreimage N t P hP colour hactive))) v

theorem paletteBlockLabel_valid {V : Type*} {N t j : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (P : Finset (Fin N)) (hP : P.card = t)
    (colour : Fin N) (hactive : colour ∉ P) (u v : V)
    (hadj : ((paletteRelabel C P hP).labelGraph colour).Adj u v) :
    paletteBlockLabel C hC P hP colour hactive u ≠
      paletteBlockLabel C hC P hP colour hactive v := by
  have hold := (paletteRelabel_adj_iff C P hP colour hactive u v).mp hadj
  exact (Classical.choice
    (hC (activeColourPreimage N t P hP colour hactive))).valid hold

theorem paletteRelabel_cliqueFree {V : Type*} {N t : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).CliqueFree 3)
    (P : Finset (Fin N)) (hP : P.card = t) (colour : Fin N) :
    ((paletteRelabel C P hP).labelGraph colour).CliqueFree 3 := by
  classical
  by_cases hactive : colour ∈ P
  · intro T hT
    obtain ⟨u, v, _, huv, _, _, _⟩ :=
      (SimpleGraph.is3Clique_iff).mp hT
    exact paletteRelabel_missing_no_adj C P hP colour hactive u v huv
  · have hgraph :
        (paletteRelabel C P hP).labelGraph colour =
          C.labelGraph (activeColourPreimage N t P hP colour hactive) := by
      ext u v
      exact paletteRelabel_adj_iff C P hP colour hactive u v
    rw [hgraph]
    exact hC _

noncomputable def deleteUnusedColour {V : Type*} {k : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (k + 1)))
    (omitted : Fin (k + 1))
    (hunused : ∀ edge : (⊤ : SimpleGraph V).edgeSet, C edge ≠ omitted) :
    SimpleGraph.TopEdgeLabeling V (Fin k) :=
  fun edge => omittedColourEquiv k omitted ⟨C edge, hunused edge⟩

def ForcesMonochromaticTriangle (n k : ℕ) : Prop :=
  ∀ C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k), ¬ TriangleFree C

noncomputable def triangleRamseyNumber (k : ℕ) : ℕ :=
  sInf {n : ℕ | ForcesMonochromaticTriangle n k}

noncomputable def differenceColourEmbedding {α : Type*} [DecidableEq α]
    (P Q : Finset α) {s : ℕ} (hcard : s ≤ (Q \ P).card) :
    Fin s ↪ α := by
  classical
  let selection : Fin s ↪ ↥(Q \ P) :=
    (Fin.castLEEmb hcard).trans (Finset.equivFin (Q \ P)).symm.toEmbedding
  exact ⟨fun i => (selection i).val,
    fun i j h => selection.injective (Subtype.ext h)⟩

theorem differenceColourEmbedding_mem {α : Type*} [DecidableEq α]
    (P Q : Finset α) {s : ℕ} (hcard : s ≤ (Q \ P).card)
    (i : Fin s) :
    differenceColourEmbedding P Q hcard i ∈ Q \ P := by
  classical
  exact ((Fin.castLEEmb hcard).trans
    (Finset.equivFin (Q \ P)).symm.toEmbedding i).property

def IsPaletteSeparated {α : Type*} [DecidableEq α]
    (s : ℕ) (family : Finset (Finset α)) : Prop :=
  ∀ P ∈ family, ∀ Q ∈ family, P ≠ Q → s ≤ (P \ Q).card

noncomputable def paletteBall {α : Type*} [DecidableEq α]
    (ambient : Finset (Finset α)) (Q : Finset α) (s : ℕ) :
    Finset (Finset α) := by
  classical
  exact ambient.filter (fun P => (P \ Q).card < s)

noncomputable def paletteShell (N t : ℕ) (Q : Finset (Fin N)) (d : ℕ) :
    Finset (Finset (Fin N)) := by
  classical
  exact ((Finset.univ : Finset (Fin N)).powersetCard t).filter
    (fun P => (P \ Q).card = d)

noncomputable def paletteShellEmbedding (N t d : ℕ)
    (Q : Finset (Fin N)) (hQ : Q.card = t) :
    ↥(paletteShell N t Q d) ↪
      (↥(Q.powersetCard d) ×
        ↥(((Finset.univ : Finset (Fin N)) \ Q).powersetCard d)) := by
  classical
  refine
    { toFun := fun P =>
        (⟨Q \ P.val, ?_⟩, ⟨P.val \ Q, ?_⟩)
      inj' := ?_ }
  · apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.sdiff_subset, ?_⟩
    have hP := (Finset.mem_filter.mp P.property)
    have hPcard := (Finset.mem_powersetCard.mp hP.1).2
    rw [Finset.card_sdiff_comm (hQ.trans hPcard.symm)]
    exact hP.2
  · apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
    · exact (Finset.mem_filter.mp P.property).2
  · intro P P' heq
    have hleft := congrArg (fun z => z.1.val) heq
    have hright := congrArg (fun z => z.2.val) heq
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ Q
    · have hmem := Finset.ext_iff.mp hleft x
      have hnegative : x ∉ P.val ↔ x ∉ P'.val := by
        simpa [hx] using hmem
      constructor
      · intro hP
        by_contra hP'
        exact (hnegative.mpr hP') hP
      · intro hP'
        by_contra hP
        exact (hnegative.mp hP) hP'
    · have hmem := Finset.ext_iff.mp hright x
      simpa [hx] using hmem

def transversalCoordinateEmbedding (j t : ℕ) (choice : Fin t → Fin j) :
    Fin t ↪ Fin (j * t) where
  toFun coordinate :=
    ((finProdFinEquiv : Fin t × Fin j ≃ Fin (t * j)).trans
      (finCongr (Nat.mul_comm t j))) (coordinate, choice coordinate)
  inj' := by
    intro x y heq
    have hpairs :=
      (((finProdFinEquiv : Fin t × Fin j ≃ Fin (t * j)).trans
        (finCongr (Nat.mul_comm t j)))).injective heq
    exact congrArg Prod.fst hpairs

noncomputable def transversalPalette (j t : ℕ) (choice : Fin t → Fin j) :
    Finset (Fin (j * t)) :=
  Finset.univ.map (transversalCoordinateEmbedding j t choice)

noncomputable def transversalPaletteEmbedding (j t : ℕ) :
    (Fin t → Fin j) ↪
      ↥((Finset.univ : Finset (Fin (j * t))).powersetCard t) := by
  classical
  refine
    { toFun := fun choice => ⟨transversalPalette j t choice, ?_⟩
      inj' := ?_ }
  · apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _, by simp [transversalPalette]⟩
  · intro choice₁ choice₂ heq
    have hpalettes :
        transversalPalette j t choice₁ =
          transversalPalette j t choice₂ :=
      congrArg Subtype.val heq
    funext coordinate
    have hmember :
        transversalCoordinateEmbedding j t choice₁ coordinate ∈
          transversalPalette j t choice₂ := by
      rw [← hpalettes]
      exact Finset.mem_map.mpr
        ⟨coordinate, Finset.mem_univ coordinate, rfl⟩
    obtain ⟨coordinate', _, hcoordinate⟩ :=
      Finset.mem_map.mp (show
        transversalCoordinateEmbedding j t choice₁ coordinate ∈
          Finset.univ.map
            (transversalCoordinateEmbedding j t choice₂) from hmember)
    have hpairs :
        (coordinate', choice₂ coordinate') =
          (coordinate, choice₁ coordinate) := by
      exact
        (((finProdFinEquiv : Fin t × Fin j ≃ Fin (t * j)).trans
          (finCongr (Nat.mul_comm t j)))).injective hcoordinate
    have hindex : coordinate' = coordinate := congrArg Prod.fst hpairs
    subst coordinate'
    exact (congrArg Prod.snd hpairs).symm

def IsCoordinateCovering {H s : ℕ}
    (f g : (Fin s → Fin H) → (Fin s → Fin H)) : Prop :=
  ∀ x y : Fin s → Fin H,
    (∃ d : Fin s, x d = f y d) ∨
      (∃ d : Fin s, y d = g x d)

noncomputable def recursiveCrossColour {K : Type*} {H s : ℕ}
    (a b : Fin s ↪ K)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (x y : Fin s → Fin H) : K := by
  classical
  exact
    if hforward : ∃ d : Fin s, x d = f y d then
      a (Fin.find (fun d => x d = f y d) hforward)
    else
      b (Fin.find (fun d => y d = g x d)
        ((hcover x y).resolve_left hforward))

theorem recursiveCrossColour_spec {K : Type*} {H s : ℕ}
    (a b : Fin s ↪ K)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (x y : Fin s → Fin H) :
    (∃ d : Fin s,
      recursiveCrossColour a b f g hcover x y = a d ∧ x d = f y d) ∨
    (∃ d : Fin s,
      recursiveCrossColour a b f g hcover x y = b d ∧ y d = g x d) := by
  classical
  by_cases hforward : ∃ d : Fin s, x d = f y d
  · let d := Fin.find (fun d => x d = f y d) hforward
    left
    refine ⟨d, ?_, Fin.find_spec hforward⟩
    simp [recursiveCrossColour, hforward, d]
  · have hbackward : ∃ d : Fin s, y d = g x d :=
      (hcover x y).resolve_left hforward
    let d := Fin.find (fun d => y d = g x d) hbackward
    right
    refine ⟨d, ?_, Fin.find_spec hbackward⟩
    simp [recursiveCrossColour, hforward, d]

theorem recursiveCrossColour_changes_membership {K : Type*} [DecidableEq K]
    {H s : ℕ} (P Q : Finset K)
    (a b : Fin s ↪ K)
    (ha : ∀ d, a d ∈ Q \ P)
    (hb : ∀ d, b d ∈ P \ Q)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (x y : Fin s → Fin H) :
    (recursiveCrossColour a b f g hcover x y ∈ P) ≠
      (recursiveCrossColour a b f g hcover x y ∈ Q) := by
  rcases recursiveCrossColour_spec a b f g hcover x y with
    ⟨d, hcolour, _⟩ | ⟨d, hcolour, _⟩
  · rw [hcolour]
    have hmem := Finset.mem_sdiff.mp (ha d)
    simp [hmem.1, hmem.2]
  · rw [hcolour]
    have hmem := Finset.mem_sdiff.mp (hb d)
    simp [hmem.1, hmem.2]

theorem recursiveCrossColour_same_left_coordinate
    {K : Type*} [DecidableEq K] {H s : ℕ}
    (P Q : Finset K) (a b : Fin s ↪ K)
    (_ha : ∀ d, a d ∈ Q \ P)
    (hb : ∀ d, b d ∈ P \ Q)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (x x' y : Fin s → Fin H) (colour : K)
    (hactive : colour ∉ P)
    (hxy : recursiveCrossColour a b f g hcover x y = colour)
    (hx'y : recursiveCrossColour a b f g hcover x' y = colour) :
    ∃ d : Fin s, colour = a d ∧ x d = x' d := by
  have select (z : Fin s → Fin H)
      (hz : recursiveCrossColour a b f g hcover z y = colour) :
      ∃ d : Fin s, colour = a d ∧ z d = f y d := by
    have hforward :=
      (recursiveCrossColour_spec a b f g hcover z y).resolve_right (by
        rintro ⟨d, hd, _⟩
        apply hactive
        rw [← hz, hd]
        exact (Finset.mem_sdiff.mp (hb d)).1)
    obtain ⟨d, hd, hforced⟩ := hforward
    exact ⟨d, hz.symm.trans hd, hforced⟩
  obtain ⟨d, hd, hforced⟩ := select x hxy
  obtain ⟨d', hd', hforced'⟩ := select x' hx'y
  have hindex : d = d' := a.injective (hd.symm.trans hd')
  exact ⟨d, hd, hforced.trans (by simpa [hindex] using hforced'.symm)⟩

theorem recursiveCrossColour_same_right_coordinate
    {K : Type*} [DecidableEq K] {H s : ℕ}
    (P Q : Finset K) (a b : Fin s ↪ K)
    (ha : ∀ d, a d ∈ Q \ P)
    (_hb : ∀ d, b d ∈ P \ Q)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (x y y' : Fin s → Fin H) (colour : K)
    (hactive : colour ∉ Q)
    (hxy : recursiveCrossColour a b f g hcover x y = colour)
    (hxy' : recursiveCrossColour a b f g hcover x y' = colour) :
    ∃ d : Fin s, colour = b d ∧ y d = y' d := by
  have select (z : Fin s → Fin H)
      (hz : recursiveCrossColour a b f g hcover x z = colour) :
      ∃ d : Fin s, colour = b d ∧ z d = g x d := by
    have hbackward :=
      (recursiveCrossColour_spec a b f g hcover x z).resolve_left (by
        rintro ⟨d, hd, _⟩
        apply hactive
        rw [← hz, hd]
        exact (Finset.mem_sdiff.mp (ha d)).1)
    obtain ⟨d, hd, hforced⟩ := hbackward
    exact ⟨d, hz.symm.trans hd, hforced⟩
  obtain ⟨d, hd, hforced⟩ := select y hxy
  obtain ⟨d', hd', hforced'⟩ := select y' hxy'
  have hindex : d = d' := b.injective (hd.symm.trans hd')
  exact ⟨d, hd, hforced.trans (by simpa [hindex] using hforced'.symm)⟩

noncomputable def paletteBlockVector {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H) (P : Finset (Fin N)) (hP : P.card = t)
    (colours : Fin s ↪ Fin N)
    (hcolours : ∀ d : Fin s, colours d ∉ P)
    (u : V) : Fin s → Fin H :=
  fun d =>
    Fin.castLE hj
      (paletteBlockLabel C hC P hP (colours d) (hcolours d) u)

noncomputable def paletteCrossColour {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (P Q : Finset (Fin N)) (hP : P.card = t) (hQ : Q.card = t)
    (a b : Fin s ↪ Fin N)
    (ha : ∀ d, a d ∈ Q \ P)
    (hb : ∀ d, b d ∈ P \ Q)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (u v : V) : Fin N :=
  recursiveCrossColour a b f g hcover
    (paletteBlockVector C hC hj P hP a
      (fun d => (Finset.mem_sdiff.mp (ha d)).2) u)
    (paletteBlockVector C hC hj Q hQ b
      (fun d => (Finset.mem_sdiff.mp (hb d)).2) v)

theorem paletteCrossColour_changes_membership
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (P Q : Finset (Fin N)) (hP : P.card = t) (hQ : Q.card = t)
    (a b : Fin s ↪ Fin N)
    (ha : ∀ d, a d ∈ Q \ P)
    (hb : ∀ d, b d ∈ P \ Q)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (u v : V) :
    (paletteCrossColour C hC hj P Q hP hQ a b ha hb f g hcover u v ∈ P) ≠
      (paletteCrossColour C hC hj P Q hP hQ a b ha hb f g hcover u v ∈ Q) := by
  exact recursiveCrossColour_changes_membership P Q a b ha hb f g hcover
    (paletteBlockVector C hC hj P hP a
      (fun d => (Finset.mem_sdiff.mp (ha d)).2) u)
    (paletteBlockVector C hC hj Q hQ b
      (fun d => (Finset.mem_sdiff.mp (hb d)).2) v)

theorem paletteCrossColour_same_left_label
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (P Q : Finset (Fin N)) (hP : P.card = t) (hQ : Q.card = t)
    (a b : Fin s ↪ Fin N)
    (ha : ∀ d, a d ∈ Q \ P)
    (hb : ∀ d, b d ∈ P \ Q)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (u u' v : V) (colour : Fin N) (hactive : colour ∉ P)
    (hu : paletteCrossColour C hC hj P Q hP hQ a b ha hb f g hcover u v =
      colour)
    (hu' : paletteCrossColour C hC hj P Q hP hQ a b ha hb f g hcover u' v =
      colour) :
    paletteBlockLabel C hC P hP colour hactive u =
      paletteBlockLabel C hC P hP colour hactive u' := by
  obtain ⟨d, hd, hequal⟩ :=
    recursiveCrossColour_same_left_coordinate P Q a b ha hb f g hcover
      (paletteBlockVector C hC hj P hP a
        (fun d => (Finset.mem_sdiff.mp (ha d)).2) u)
      (paletteBlockVector C hC hj P hP a
        (fun d => (Finset.mem_sdiff.mp (ha d)).2) u')
      (paletteBlockVector C hC hj Q hQ b
        (fun d => (Finset.mem_sdiff.mp (hb d)).2) v)
      colour hactive hu hu'
  change
    Fin.castLE hj
        (paletteBlockLabel C hC P hP (a d)
          ((Finset.mem_sdiff.mp (ha d)).2) u) =
      Fin.castLE hj
        (paletteBlockLabel C hC P hP (a d)
          ((Finset.mem_sdiff.mp (ha d)).2) u') at hequal
  have hlabels := Fin.castLE_injective hj hequal
  simpa [hd] using hlabels

theorem paletteCrossColour_same_right_label
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (P Q : Finset (Fin N)) (hP : P.card = t) (hQ : Q.card = t)
    (a b : Fin s ↪ Fin N)
    (ha : ∀ d, a d ∈ Q \ P)
    (hb : ∀ d, b d ∈ P \ Q)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (u v v' : V) (colour : Fin N) (hactive : colour ∉ Q)
    (hv : paletteCrossColour C hC hj P Q hP hQ a b ha hb f g hcover u v =
      colour)
    (hv' : paletteCrossColour C hC hj P Q hP hQ a b ha hb f g hcover u v' =
      colour) :
    paletteBlockLabel C hC Q hQ colour hactive v =
      paletteBlockLabel C hC Q hQ colour hactive v' := by
  obtain ⟨d, hd, hequal⟩ :=
    recursiveCrossColour_same_right_coordinate P Q a b ha hb f g hcover
      (paletteBlockVector C hC hj P hP a
        (fun d => (Finset.mem_sdiff.mp (ha d)).2) u)
      (paletteBlockVector C hC hj Q hQ b
        (fun d => (Finset.mem_sdiff.mp (hb d)).2) v)
      (paletteBlockVector C hC hj Q hQ b
        (fun d => (Finset.mem_sdiff.mp (hb d)).2) v')
      colour hactive hv hv'
  change
    Fin.castLE hj
        (paletteBlockLabel C hC Q hQ (b d)
          ((Finset.mem_sdiff.mp (hb d)).2) v) =
      Fin.castLE hj
        (paletteBlockLabel C hC Q hQ (b d)
          ((Finset.mem_sdiff.mp (hb d)).2) v') at hequal
  have hlabels := Fin.castLE_injective hj hequal
  simpa [hd] using hlabels

structure PaletteBlockCertificate {I V K : Type*} [DecidableEq K]
    (C : SimpleGraph.TopEdgeLabeling (I × V) K) (j : ℕ) where
  palette : I → Finset K
  label : ∀ (i : I) (colour : K), colour ∉ palette i → V → Fin j
  internal_no_triangle :
    ∀ (i : I) (colour : K) (u v w : V),
      ¬ ((C.labelGraph colour).Adj (i, u) (i, v) ∧
         (C.labelGraph colour).Adj (i, u) (i, w) ∧
         (C.labelGraph colour).Adj (i, v) (i, w))
  missing_has_no_internal_edge :
    ∀ (i : I) (colour : K), colour ∈ palette i →
      ∀ u v : V, ¬ (C.labelGraph colour).Adj (i, u) (i, v)
  internal_labels_proper :
    ∀ (i : I) (colour : K) (hactive : colour ∉ palette i)
      (u v : V),
      (C.labelGraph colour).Adj (i, u) (i, v) →
        label i colour hactive u ≠ label i colour hactive v
  cross_edge_changes_membership :
    ∀ (i i' : I) (colour : K) (u v : V), i ≠ i' →
      (C.labelGraph colour).Adj (i, u) (i', v) →
        (colour ∈ palette i) ≠ (colour ∈ palette i')
  cross_edges_force_equal_active_labels :
    ∀ (i i' : I) (colour : K) (u u' v : V)
      (_hne : i ≠ i') (hactive : colour ∉ palette i),
      (C.labelGraph colour).Adj (i, u) (i', v) →
      (C.labelGraph colour).Adj (i, u') (i', v) →
        label i colour hactive u = label i colour hactive u'

namespace PaletteBlockCertificate

noncomputable def globalLabel {I V K : Type*} [DecidableEq K]
    {C : SimpleGraph.TopEdgeLabeling (I × V) K} {j : ℕ}
    (certificate : PaletteBlockCertificate C j) (colour : K)
    (x : I × V) : Fin (j + 1) := by
  classical
  exact
    if h : colour ∈ certificate.palette x.1 then
      Fin.last j
    else
      (certificate.label x.1 colour h x.2).castSucc


end PaletteBlockCertificate

noncomputable def paletteFamilyForwardList {N s : ℕ}
    (family : Finset (Finset (Fin N)))
    (hseparated : IsPaletteSeparated s family)
    (i i' : ↥family) (hne : i ≠ i') : Fin s ↪ Fin N :=
  differenceColourEmbedding i.val i'.val
    (hseparated i'.val i'.property i.val i.property
      (fun heq => hne (Subtype.ext heq.symm)))

theorem paletteFamilyForwardList_mem {N s : ℕ}
    (family : Finset (Finset (Fin N)))
    (hseparated : IsPaletteSeparated s family)
    (i i' : ↥family) (hne : i ≠ i') (d : Fin s) :
    paletteFamilyForwardList family hseparated i i' hne d ∈
      i'.val \ i.val := by
  unfold paletteFamilyForwardList
  exact differenceColourEmbedding_mem _ _ _ _

noncomputable def paletteFamilyCrossColour
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (i i' : ↥family) (hne : i ≠ i') (u v : V) : Fin N :=
  paletteCrossColour C hC hj i.val i'.val
    (hcard i.val i.property) (hcard i'.val i'.property)
    (paletteFamilyForwardList family hseparated i i' hne)
    (paletteFamilyForwardList family hseparated i' i hne.symm)
    (paletteFamilyForwardList_mem family hseparated i i' hne)
    (paletteFamilyForwardList_mem family hseparated i' i hne.symm)
    f g hcover u v

theorem paletteFamilyCrossColour_changes_membership
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (i i' : ↥family) (hne : i ≠ i') (u v : V) :
    (paletteFamilyCrossColour C hC hj family hcard hseparated
        f g hcover i i' hne u v ∈ i.val) ≠
      (paletteFamilyCrossColour C hC hj family hcard hseparated
        f g hcover i i' hne u v ∈ i'.val) := by
  exact paletteCrossColour_changes_membership C hC hj i.val i'.val
    (hcard i.val i.property) (hcard i'.val i'.property)
    (paletteFamilyForwardList family hseparated i i' hne)
    (paletteFamilyForwardList family hseparated i' i hne.symm)
    (paletteFamilyForwardList_mem family hseparated i i' hne)
    (paletteFamilyForwardList_mem family hseparated i' i hne.symm)
    f g hcover u v

theorem paletteFamilyCrossColour_same_left_label
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (i i' : ↥family) (hne : i ≠ i')
    (u u' v : V) (colour : Fin N) (hactive : colour ∉ i.val)
    (hu : paletteFamilyCrossColour C hC hj family hcard hseparated
      f g hcover i i' hne u v = colour)
    (hu' : paletteFamilyCrossColour C hC hj family hcard hseparated
      f g hcover i i' hne u' v = colour) :
    paletteBlockLabel C hC i.val (hcard i.val i.property)
        colour hactive u =
      paletteBlockLabel C hC i.val (hcard i.val i.property)
        colour hactive u' := by
  exact paletteCrossColour_same_left_label C hC hj i.val i'.val
    (hcard i.val i.property) (hcard i'.val i'.property)
    (paletteFamilyForwardList family hseparated i i' hne)
    (paletteFamilyForwardList family hseparated i' i hne.symm)
    (paletteFamilyForwardList_mem family hseparated i i' hne)
    (paletteFamilyForwardList_mem family hseparated i' i hne.symm)
    f g hcover u u' v colour hactive hu hu'

theorem paletteFamilyCrossColour_same_right_label
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (i i' : ↥family) (hne : i ≠ i')
    (u v v' : V) (colour : Fin N) (hactive : colour ∉ i'.val)
    (hv : paletteFamilyCrossColour C hC hj family hcard hseparated
      f g hcover i i' hne u v = colour)
    (hv' : paletteFamilyCrossColour C hC hj family hcard hseparated
      f g hcover i i' hne u v' = colour) :
    paletteBlockLabel C hC i'.val (hcard i'.val i'.property)
        colour hactive v =
      paletteBlockLabel C hC i'.val (hcard i'.val i'.property)
        colour hactive v' := by
  exact paletteCrossColour_same_right_label C hC hj i.val i'.val
    (hcard i.val i.property) (hcard i'.val i'.property)
    (paletteFamilyForwardList family hseparated i i' hne)
    (paletteFamilyForwardList family hseparated i' i hne.symm)
    (paletteFamilyForwardList_mem family hseparated i i' hne)
    (paletteFamilyForwardList_mem family hseparated i' i hne.symm)
    f g hcover u v v' colour hactive hv hv'

noncomputable def recursivePaletteEdgeColour
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (x y : ↥family × V) (hne : x ≠ y) : Fin N := by
  classical
  exact
    if hsame : x.1 = y.1 then
      (paletteRelabel C x.1.val (hcard x.1.val x.1.property)).get
        x.2 y.2 (fun heq => hne (Prod.ext hsame heq))
    else if horder :
        (Finset.equivFin family) x.1 < (Finset.equivFin family) y.1 then
      paletteFamilyCrossColour C hC hj family hcard hseparated
        f g hcover x.1 y.1 hsame x.2 y.2
    else
      paletteFamilyCrossColour C hC hj family hcard hseparated
        f g hcover y.1 x.1 (Ne.symm hsame) y.2 x.2

theorem recursivePaletteEdgeColour_symm
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (x y : ↥family × V) (hne : x ≠ y) :
    recursivePaletteEdgeColour C hC hj family hcard hseparated
        f g hcover y x hne.symm =
      recursivePaletteEdgeColour C hC hj family hcard hseparated
        f g hcover x y hne := by
  classical
  rcases x with ⟨i, u⟩
  rcases y with ⟨i', v⟩
  by_cases hsame : i = i'
  · subst i'
    have huv : u ≠ v := fun heq => hne (Prod.ext rfl heq)
    simpa [recursivePaletteEdgeColour] using
      (SimpleGraph.EdgeLabeling.get_comm
        (C := paletteRelabel C i.val (hcard i.val i.property))
        u v (Ne.symm huv))
  · have hrank :
        (Finset.equivFin family) i ≠ (Finset.equivFin family) i' :=
      fun heq => hsame ((Finset.equivFin family).injective heq)
    rcases lt_or_gt_of_ne hrank with horder | horder
    · simp [recursivePaletteEdgeColour, hsame, Ne.symm hsame,
        horder, not_lt_of_gt horder]
    · simp [recursivePaletteEdgeColour, hsame, Ne.symm hsame,
        horder, not_lt_of_gt horder]

noncomputable def recursivePaletteColouring
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g) :
    SimpleGraph.TopEdgeLabeling (↥family × V) (Fin N) :=
  SimpleGraph.EdgeLabeling.mk
    (fun x y hne => recursivePaletteEdgeColour C hC hj family hcard
      hseparated f g hcover x y hne)
    (fun x y hne => recursivePaletteEdgeColour_symm C hC hj family hcard
      hseparated f g hcover x y hne)

theorem recursivePaletteColouring_get
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (x y : ↥family × V) (hne : x ≠ y) :
    (recursivePaletteColouring C hC hj family hcard hseparated
      f g hcover).get x y hne =
        recursivePaletteEdgeColour C hC hj family hcard hseparated
          f g hcover x y hne := by
  rfl

theorem recursivePaletteColouring_internal_adj_iff
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (i : ↥family) (colour : Fin N) (u v : V) :
    ((recursivePaletteColouring C hC hj family hcard hseparated
        f g hcover).labelGraph colour).Adj (i, u) (i, v) ↔
      ((paletteRelabel C i.val (hcard i.val i.property)).labelGraph
        colour).Adj u v := by
  constructor
  · intro hadj
    obtain ⟨hne, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj (i, u) (i, v)).mp hadj
    have huv : u ≠ v := by
      intro heq
      exact hne (Prod.ext rfl heq)
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mpr
    refine ⟨huv, ?_⟩
    rw [recursivePaletteColouring_get] at hcolour
    simpa [recursivePaletteEdgeColour] using hcolour
  · intro hadj
    obtain ⟨huv, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mp hadj
    have hne : (i, u) ≠ (i, v) := by
      intro heq
      exact huv (congrArg Prod.snd heq)
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj (i, u) (i, v)).mpr
    refine ⟨hne, ?_⟩
    rw [recursivePaletteColouring_get]
    simpa [recursivePaletteEdgeColour] using hcolour

theorem recursivePaletteColouring_cross_adj_iff_of_lt
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g)
    (i i' : ↥family) (hne : i ≠ i')
    (horder : (Finset.equivFin family) i < (Finset.equivFin family) i')
    (colour : Fin N) (u v : V) :
    ((recursivePaletteColouring C hC hj family hcard hseparated
        f g hcover).labelGraph colour).Adj (i, u) (i', v) ↔
      paletteFamilyCrossColour C hC hj family hcard hseparated
        f g hcover i i' hne u v = colour := by
  constructor
  · intro hadj
    obtain ⟨hpair, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj (i, u) (i', v)).mp hadj
    rw [recursivePaletteColouring_get] at hcolour
    simpa [recursivePaletteEdgeColour, hne, horder] using hcolour
  · intro hcolour
    have hpair : (i, u) ≠ (i', v) := by
      intro heq
      exact hne (congrArg Prod.fst heq)
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj (i, u) (i', v)).mpr
    refine ⟨hpair, ?_⟩
    rw [recursivePaletteColouring_get]
    simpa [recursivePaletteEdgeColour, hne, horder] using hcolour

theorem paletteFamily_reverse_rank_lt {N : ℕ}
    (family : Finset (Finset (Fin N)))
    (i i' : ↥family) (hne : i ≠ i')
    (hnot : ¬ (Finset.equivFin family) i <
      (Finset.equivFin family) i') :
    (Finset.equivFin family) i' < (Finset.equivFin family) i := by
  have hrank : (Finset.equivFin family) i ≠ (Finset.equivFin family) i' := by
    intro heq
    exact hne ((Finset.equivFin family).injective heq)
  exact lt_of_le_of_ne (le_of_not_gt hnot) hrank.symm

noncomputable def recursivePaletteCertificate
    {V : Type*} {N t j H s : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V (Fin (N - t)))
    (htriangle : ∀ colour : Fin (N - t),
      (C.labelGraph colour).CliqueFree 3)
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated s family)
    (f g : (Fin s → Fin H) → (Fin s → Fin H))
    (hcover : IsCoordinateCovering f g) :
    PaletteBlockCertificate
      (recursivePaletteColouring C hC hj family hcard hseparated
        f g hcover) j := by
  classical
  refine
    { palette := fun i => i.val
      label := fun i colour hactive =>
        paletteBlockLabel C hC i.val (hcard i.val i.property)
          colour hactive
      internal_no_triangle := ?_
      missing_has_no_internal_edge := ?_
      internal_labels_proper := ?_
      cross_edge_changes_membership := ?_
      cross_edges_force_equal_active_labels := ?_ }
  · intro i colour u v w htriangle'
    obtain ⟨huv, huw, hvw⟩ := htriangle'
    have huv' :=
      (recursivePaletteColouring_internal_adj_iff C hC hj family
        hcard hseparated f g hcover i colour u v).mp huv
    have huw' :=
      (recursivePaletteColouring_internal_adj_iff C hC hj family
        hcard hseparated f g hcover i colour u w).mp huw
    have hvw' :=
      (recursivePaletteColouring_internal_adj_iff C hC hj family
        hcard hseparated f g hcover i colour v w).mp hvw
    exact (paletteRelabel_cliqueFree C htriangle i.val
      (hcard i.val i.property) colour) {u, v, w}
        ((SimpleGraph.is3Clique_triple_iff).mpr ⟨huv', huw', hvw'⟩)
  · intro i colour hmissing u v hadj
    exact paletteRelabel_missing_no_adj C i.val
      (hcard i.val i.property) colour hmissing u v
        ((recursivePaletteColouring_internal_adj_iff C hC hj family
          hcard hseparated f g hcover i colour u v).mp hadj)
  · intro i colour hactive u v hadj
    exact paletteBlockLabel_valid C hC i.val
      (hcard i.val i.property) colour hactive u v
        ((recursivePaletteColouring_internal_adj_iff C hC hj family
          hcard hseparated f g hcover i colour u v).mp hadj)
  · intro i i' colour u v hne hadj
    by_cases horder :
        (Finset.equivFin family) i < (Finset.equivFin family) i'
    · have hcolour :=
        (recursivePaletteColouring_cross_adj_iff_of_lt C hC hj family
          hcard hseparated f g hcover i i' hne horder colour u v).mp hadj
      have hchange := paletteFamilyCrossColour_changes_membership
        C hC hj family hcard hseparated f g hcover i i' hne u v
      rw [hcolour] at hchange
      exact hchange
    · have hreverse := paletteFamily_reverse_rank_lt family i i' hne horder
      have hcolour :=
        (recursivePaletteColouring_cross_adj_iff_of_lt C hC hj family
          hcard hseparated f g hcover i' i (Ne.symm hne)
            hreverse colour v u).mp hadj.symm
      have hchange := paletteFamilyCrossColour_changes_membership
        C hC hj family hcard hseparated f g hcover i' i (Ne.symm hne) v u
      rw [hcolour] at hchange
      exact Ne.symm hchange
  · intro i i' colour u u' v hne hactive hadj hadj'
    by_cases horder :
        (Finset.equivFin family) i < (Finset.equivFin family) i'
    · have hu :=
        (recursivePaletteColouring_cross_adj_iff_of_lt C hC hj family
          hcard hseparated f g hcover i i' hne horder colour u v).mp hadj
      have hu' :=
        (recursivePaletteColouring_cross_adj_iff_of_lt C hC hj family
          hcard hseparated f g hcover i i' hne horder colour u' v).mp hadj'
      exact paletteFamilyCrossColour_same_left_label C hC hj family
        hcard hseparated f g hcover i i' hne u u' v colour hactive hu hu'
    · have hreverse := paletteFamily_reverse_rank_lt family i i' hne horder
      have hu :=
        (recursivePaletteColouring_cross_adj_iff_of_lt C hC hj family
          hcard hseparated f g hcover i' i (Ne.symm hne)
            hreverse colour v u).mp hadj.symm
      have hu' :=
        (recursivePaletteColouring_cross_adj_iff_of_lt C hC hj family
          hcard hseparated f g hcover i' i (Ne.symm hne)
            hreverse colour v u').mp hadj'.symm
      exact paletteFamilyCrossColour_same_right_label C hC hj family
        hcard hseparated f g hcover i' i (Ne.symm hne)
          v u u' colour hactive hu hu'

def IsSaturated {H m s : ℕ}
    (A : Fin s → (Fin m → Fin H) → Fin H) : Prop :=
  ∀ T : Finset (Fin m → Fin H), T.card = m + 1 →
    ∃ row : Fin s, ∀ symbol : Fin H,
      ∃ column ∈ T, A row column = symbol

def RowCovers {H m : ℕ}
    (T : Finset (Fin m → Fin H))
    (row : (Fin m → Fin H) → Fin H) : Prop :=
  ∀ symbol : Fin H, ∃ column ∈ T, row column = symbol

noncomputable def badSaturationRows (H m : ℕ)
    (T : Finset (Fin m → Fin H)) :
    Finset ((Fin m → Fin H) → Fin H) := by
  classical
  exact Finset.univ.filter (fun row => ¬ RowCovers T row)

noncomputable def missingSymbolRows (H m : ℕ)
    (T : Finset (Fin m → Fin H)) (symbol : Fin H) :
    Finset ((Fin m → Fin H) → Fin H) := by
  classical
  exact Fintype.piFinset fun column =>
    if column ∈ T then (Finset.univ : Finset (Fin H)).erase symbol
    else Finset.univ

noncomputable def badSaturationMatrices (H m s : ℕ)
    (T : Finset (Fin m → Fin H)) :
    Finset (Fin s → (Fin m → Fin H) → Fin H) :=
  Fintype.piFinset fun _ : Fin s => badSaturationRows H m T

noncomputable def saturatedMatrixWidth (H : ℕ) : ℕ :=
  ⌈2 * (H : ℝ) * Real.log (H : ℝ)⌉₊

noncomputable def saturatedMatrixRows (H : ℕ) : ℕ :=
  saturatedMatrixWidth H * (saturatedMatrixWidth H + 1) + 1

noncomputable def exceptionalColumns {H m s : ℕ}
    (A : Fin s → (Fin m → Fin H) → Fin H)
    (y : Fin s → Fin H) : Finset (Fin m → Fin H) := by
  classical
  exact Finset.univ.filter (fun z => ∀ row : Fin s, A row z ≠ y row)

theorem mem_exceptionalColumns {H m s : ℕ}
    (A : Fin s → (Fin m → Fin H) → Fin H)
    (y : Fin s → Fin H) (z : Fin m → Fin H) :
    z ∈ exceptionalColumns A y ↔
      ∀ row : Fin s, A row z ≠ y row := by
  classical
  simp [exceptionalColumns]

theorem card_exceptionalColumns_le {H m s : ℕ}
    (A : Fin s → (Fin m → Fin H) → Fin H)
    (hA : IsSaturated A) (y : Fin s → Fin H) :
    (exceptionalColumns A y).card ≤ m := by
  classical
  by_contra hnot
  have hcard : m + 1 ≤ (exceptionalColumns A y).card := by
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcard
  obtain ⟨row, hrow⟩ := hA T hTcard
  obtain ⟨z, hzT, hz⟩ := hrow (y row)
  have hzexception : z ∈ exceptionalColumns A y := hTsub hzT
  exact (mem_exceptionalColumns A y z).mp hzexception row hz

noncomputable def exceptionalColumnIndex {H m s : ℕ}
    (A : Fin s → (Fin m → Fin H) → Fin H)
    (hA : IsSaturated A) (y : Fin s → Fin H) :
    (exceptionalColumns A y) ↪ Fin m :=
  (Finset.equivFin (exceptionalColumns A y)).toEmbedding.trans
    (Fin.castLEEmb (card_exceptionalColumns_le A hA y))

def backwardGuess {H m s : ℕ}
    (A : Fin s → (Fin m → Fin H) → Fin H)
    (hms : m ≤ s) (x : Fin s → Fin H) : Fin s → Fin H :=
  fun row => A row (fun coordinate => x (Fin.castLE hms coordinate))

noncomputable def forwardGuess {H m s : ℕ}
    (A : Fin s → (Fin m → Fin H) → Fin H)
    (hA : IsSaturated A) (hH : 0 < H) (hms : m ≤ s)
    (y : Fin s → Fin H) (row : Fin s) : Fin H := by
  classical
  let index := exceptionalColumnIndex A hA y
  exact
    if h : ∃ z : exceptionalColumns A y,
        Fin.castLE hms (index z) = row then
      (Classical.choose h).val (index (Classical.choose h))
    else
      ⟨0, hH⟩

def singletonZeroColouring :
    SimpleGraph.TopEdgeLabeling (Fin 1) (Fin 0) := by
  intro edge
  exfalso
  obtain ⟨edge, hedge⟩ := edge
  induction edge using Sym2.inductionOn with
  | _ u v =>
      exact hedge (Subsingleton.elim u v)

def PaletteGrowthBound (a s j n : ℕ) : Prop :=
  (j.factorial : ℝ) ^ (a * s) ≤
    (n : ℝ) * (s : ℝ) ^ j *
      (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^ (s * j) *
      (j.factorial : ℝ) ^ s

noncomputable def paletteLogWidth (H : ℕ) : ℕ :=
  max 2 ⌈Real.log (H : ℝ)⌉₊

noncomputable def paletteColourCount (H : ℕ) : ℕ :=
  H * (paletteLogWidth H * saturatedMatrixRows H)

end Erdos183


