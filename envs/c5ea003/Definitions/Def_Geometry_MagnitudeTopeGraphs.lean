-- Prove2me | Definitions.Def_Geometry_MagnitudeTopeGraphs
-- name    : Geometry_MagnitudeTopeGraphs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:40:11.891054+00:00
-- url     : https://prove2.me/theorems/9cb58f5c-d435-4556-bab5-22e175cd3306
-- title:
--   Aether Catalog definitions — Geometry_MagnitudeTopeGraphs
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.MagnitudeTopeGraphs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/MagnitudeTopeGraphs.lean by skeleton subtraction
import Mathlib
/-
# Magnitude homology of tope graphs

This file develops, from scratch, a chain of results around the magnitude homology of
*tope graphs* of real hyperplane arrangements, following the theme of the paper
"Magnitude homology of tope graphs".

The development is organised as a strictly increasing chain of results, each one using
the previous ones:

1. **The coordinate (Boolean) arrangement.** For the real arrangement of the `n`
   coordinate hyperplanes `{x : xᵢ = 0}` in `ℝⁿ`, the chambers (topes) are indexed by
   subsets `s ⊆ Fin n` (the set of coordinates that are positive). We prove that these
   chambers are nonempty, convex, pairwise disjoint, avoid all hyperplanes, and — the key
   combinatorial fact — that the set of hyperplanes *separating* two chambers is exactly
   the symmetric difference of the indexing sets.

2. **The tope graph.** Two topes are adjacent when exactly one hyperplane separates them.
   We prove that the graph distance of the resulting tope graph is exactly the number of
   separating hyperplanes, `dist s t = |s Δ t|`, and deduce connectivity.

3. **Magnitude chains in low degree.** For an arbitrary connected simple graph `G` we
   introduce the magnitude chain generators in degrees 1 and 2 and the magnitude
   differential `δ₂`, and prove:
   * `Gen2` is empty in lengths `< 2` (chains are "long"),
   * hence `MH_{1,1}(G)` is the free abelian group on the ordered edges of `G`,
   * `δ₂` is surjective in every length `ℓ ≥ 2`, hence `MH_{1,ℓ}(G) = 0`.
   The last statement is the degree-1 case of *diagonality*, which the paper establishes
   in all degrees for tope graphs.

4. **Diagonal cycles in bidegree (2,2).** The ordered edges of `G` embed into the cycles
   `ker δ₂` in length 2 via `(x,y) ↦ (x,y,x)`.

5. **Application to the tope graph.** Combining everything: for the coordinate
   arrangement in `ℝⁿ` the tope graph is connected, `MH_{1,1}` is free of rank `2ⁿ · n`,
   `MH_{1,ℓ} = 0` for `ℓ ≥ 2`, and the group of `(2,2)`-cycles is nontrivial for `n ≥ 1`.
   We also count the chain groups: `MC_{1,ℓ}` has rank `2ⁿ · C(n,ℓ)` and `MC_{2,2}` has
   rank `2ⁿ · n²`, and we exhibit the splitting
   `MH_{2,2} ⊕ ℤ^{2ⁿ·C(n,2)} ≅ ℤ^{2ⁿ·n²}` — i.e. `MH_{2,2}` has rank `2ⁿ · n(n+1)/2`,
   which is `2ⁿ` times the value at `2` of the Hilbert function of a polynomial ring in
   `n` variables, as predicted by the Stanley–Reisner description.

6. **The Coxeter picture.** The coordinate arrangement is the reflection arrangement of
   the Coxeter group `(ℤ/2)ⁿ` (type `A₁ⁿ`). We prove that graph isomorphisms are
   isometries, that the tope graph is isomorphic to the Cayley graph of `(ℤ/2)ⁿ` with
   respect to its Coxeter generators, and transport all the magnitude homology
   computations of stage 5 to that Cayley graph.

Everything below is self-contained (only `Mathlib` is imported).
-/


namespace MagnitudeTope

open scoped Classical

/-! ## 1. Chambers of the coordinate arrangement in `ℝⁿ` -/

section Chambers

variable {n : ℕ}

/-- The chamber (tope) of the coordinate hyperplane arrangement `{xᵢ = 0}` in `ℝⁿ`
associated with the sign vector encoded by `s`: the coordinates in `s` are positive and
the coordinates outside `s` are negative. -/
def chamber (s : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {x | (∀ i ∈ s, 0 < x i) ∧ ∀ i ∉ s, x i < 0}







end Chambers

/-! ## 2. The tope graph and its distance function -/

section TopeGraph

variable {n : ℕ}

/-- The **tope graph** of the coordinate arrangement in `ℝⁿ`: two topes are adjacent when
exactly one hyperplane of the arrangement separates them. By
`mem_symmDiff_iff_separated`, the separating set of the topes `s` and `t` is `s Δ t`. -/
def topeGraph (n : ℕ) : SimpleGraph (Finset (Fin n)) where
  Adj s t := (symmDiff s t).card = 1
  symm := by intro s t h; rwa [symmDiff_comm]
  loopless := by constructor; intro s h; simp at h


/-- Flipping the `i`-th sign of a tope produces an adjacent tope. -/
lemma tope_adj_flip (s : Finset (Fin n)) (i : Fin n) :
    (topeGraph n).Adj s (symmDiff s {i}) := by
  show (symmDiff s (symmDiff s {i})).card = 1
  simp [symmDiff_symmDiff_cancel_left]

/-- Flipping a coordinate in the separating set decreases the separation number by one. -/
lemma sd_step (s t : Finset (Fin n)) (i : Fin n) (hi : i ∈ symmDiff s t) :
    (symmDiff (symmDiff s {i}) t).card + 1 = (symmDiff s t).card := by
  have hi' := Finset.mem_symmDiff.mp hi
  have h1 : symmDiff (symmDiff s ({i} : Finset (Fin n))) t = symmDiff (symmDiff s t) {i} := by
    rw [symmDiff_assoc, symmDiff_assoc, symmDiff_comm ({i} : Finset (Fin n)) t]
  have h2 : symmDiff (symmDiff s t) ({i} : Finset (Fin n)) = (symmDiff s t).erase i := by
    ext j
    by_cases hj : j = i <;> simp [hj, Finset.mem_erase, Finset.mem_symmDiff]
    tauto
  have h3 := Finset.card_pos.mpr ⟨i, hi⟩
  rw [h1, h2, Finset.card_erase_of_mem hi]
  omega

/-- There is a walk between two topes of length at most their separation number. -/
lemma exists_walk_card (s t : Finset (Fin n)) :
    ∃ p : (topeGraph n).Walk s t, p.length ≤ (symmDiff s t).card := by
  generalize hm : (symmDiff s t).card = m
  induction m using Nat.strong_induction_on generalizing s with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      have hst : s = t := by
        have : symmDiff s t = ∅ := Finset.card_eq_zero.mp hm
        simpa [symmDiff_eq_bot] using this
      subst hst
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
    · obtain ⟨i, hi⟩ := Finset.card_pos.mp (hm ▸ h)
      have key := sd_step s t i hi
      obtain ⟨p, hp⟩ := ih ((symmDiff (symmDiff s {i}) t).card) (by omega) (symmDiff s {i}) rfl
      exact ⟨SimpleGraph.Walk.cons (tope_adj_flip s i) p, by
        simp only [SimpleGraph.Walk.length_cons]; omega⟩

/-- Any walk between two topes has length at least their separation number. -/
lemma card_le_walk_length {s t : Finset (Fin n)} (p : (topeGraph n).Walk s t) :
    (symmDiff s t).card ≤ p.length := by
  induction p with
  | nil => simp
  | cons h q ih =>
    rename_i a b c
    have htri : (symmDiff a c).card ≤ (symmDiff a b).card + (symmDiff b c).card :=
      calc (symmDiff a c).card ≤ (symmDiff a b ∪ symmDiff b c).card :=
            Finset.card_le_card (by simpa using symmDiff_triangle a b c)
        _ ≤ _ := Finset.card_union_le _ _
    have hab : (symmDiff a b).card = 1 := h
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- **The tope graph is an isometric model of the separation metric**: the graph distance
between two topes equals the number of hyperplanes separating them. -/
theorem topeGraph_dist (s t : Finset (Fin n)) :
    (topeGraph n).dist s t = (symmDiff s t).card := by
  obtain ⟨p, hp⟩ := exists_walk_card s t
  refine le_antisymm ((SimpleGraph.dist_le p).trans hp) ?_
  have hr : (topeGraph n).Reachable s t := ⟨p⟩
  obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_dist
  exact hq ▸ card_le_walk_length q


end TopeGraph

/-! ## 3. Magnitude chains and magnitude homology in degree 1 -/

section Magnitude

variable {V : Type*} {G : SimpleGraph V}

/-- Generators of the magnitude chain group `MC_{1,ℓ}(G)`: ordered pairs of distinct
vertices at distance `ℓ`. -/
def Gen1 (G : SimpleGraph V) (ℓ : ℕ) : Type _ :=
  {p : V × V // p.1 ≠ p.2 ∧ G.dist p.1 p.2 = ℓ}

/-- Generators of the magnitude chain group `MC_{2,ℓ}(G)`: triples of vertices with
consecutive entries distinct and total length `ℓ`. -/
def Gen2 (G : SimpleGraph V) (ℓ : ℕ) : Type _ :=
  {p : V × V × V // p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2 ∧
      G.dist p.1 p.2.1 + G.dist p.2.1 p.2.2 = ℓ}

lemma dist_pos_of_ne (hG : G.Connected) {x y : V} (h : x ≠ y) : 0 < G.dist x y := by
  rcases Nat.eq_zero_or_pos (G.dist x y) with h0 | h0
  · rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp h0 with h1 | h1
    · exact absurd h1 h
    · exact absurd (hG.preconnected x y) h1
  · exact h0




/-- The magnitude differential on a degree-2 generator: delete the middle vertex, keeping
the result only if the total length is preserved. -/
noncomputable def delta2gen (hG : G.Connected) (ℓ : ℕ) (g : Gen2 G ℓ) : Gen1 G ℓ →₀ ℤ :=
  if h : G.dist g.1.1 g.1.2.2 = G.dist g.1.1 g.1.2.1 + G.dist g.1.2.1 g.1.2.2 then
    Finsupp.single ⟨(g.1.1, g.1.2.2), by
      refine ⟨?_, by rw [h]; exact g.2.2.2⟩
      rintro he
      have h0 : G.dist g.1.1 g.1.2.2 = 0 := by rw [he]; simp
      have := dist_pos_of_ne hG g.2.1
      omega⟩ 1
  else 0

/-- The magnitude differential `δ₂ : MC_{2,ℓ}(G) → MC_{1,ℓ}(G)`. -/
noncomputable def delta2 (hG : G.Connected) (ℓ : ℕ) :
    (Gen2 G ℓ →₀ ℤ) →ₗ[ℤ] (Gen1 G ℓ →₀ ℤ) :=
  Finsupp.linearCombination ℤ (delta2gen hG ℓ)

/-- Magnitude homology `MH_{1,ℓ}(G)`. Since the differential out of degree 1 is zero,
this is the cokernel of `δ₂`. -/
noncomputable abbrev MH1 (hG : G.Connected) (ℓ : ℕ) : Type _ :=
  (Gen1 G ℓ →₀ ℤ) ⧸ LinearMap.range (delta2 hG ℓ)



/-- The degree-1 magnitude generators of length 1 are exactly the ordered edges. -/
def Gen1_one_equiv (G : SimpleGraph V) : Gen1 G 1 ≃ {p : V × V // G.Adj p.1 p.2} where
  toFun g := ⟨g.1, SimpleGraph.dist_eq_one_iff_adj.mp g.2.2⟩
  invFun p := ⟨p.1, p.2.ne, SimpleGraph.dist_eq_one_iff_adj.mpr p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl





end Magnitude

/-! ## 4. Diagonal cycles in bidegree `(2,2)` -/

section Diagonal

variable {V : Type*} {G : SimpleGraph V}

/-- The map sending an ordered edge `(x,y)` to the degree-2 chain `(x,y,x)`. -/
def diagGen (g : Gen1 G 1) : Gen2 G 2 :=
  ⟨(g.1.1, g.1.2, g.1.1), g.2.1, (g.2.1).symm, by
    have h1 : G.dist g.1.1 g.1.2 = 1 := g.2.2
    have h2 : G.dist g.1.2 g.1.1 = 1 := by rw [SimpleGraph.dist_comm]; exact h1
    show G.dist g.1.1 g.1.2 + G.dist g.1.2 g.1.1 = 2
    omega⟩


/-- The induced embedding of the free abelian group on ordered edges into the degree-2
magnitude chains of length 2. -/
noncomputable def diagIncl (G : SimpleGraph V) :
    (Gen1 G 1 →₀ ℤ) →ₗ[ℤ] (Gen2 G 2 →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ diagGen




end Diagonal

/-! ## 5. Application: magnitude homology of the tope graph -/

section Application

variable {n : ℕ}

/-- Ordered edges of the tope graph are pairs (tope, flipped coordinate). -/
noncomputable def topeEdgeEquiv (n : ℕ) :
    Finset (Fin n) × Fin n ≃
      {p : Finset (Fin n) × Finset (Fin n) // (topeGraph n).Adj p.1 p.2} := by
  apply Equiv.ofBijective (fun si => ⟨(si.1, symmDiff si.1 {si.2}), by
    show (symmDiff si.1 (symmDiff si.1 {si.2})).card = 1
    simp [symmDiff_symmDiff_cancel_left]⟩)
  constructor
  · rintro ⟨s, i⟩ ⟨s', i'⟩ h
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    have : ({i} : Finset (Fin n)) = {i'} := by
      have := congrArg (fun t => symmDiff s t) h2
      simpa [symmDiff_symmDiff_cancel_left] using this
    simp_all
  · rintro ⟨⟨s, t⟩, h⟩
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
    refine ⟨(s, i), ?_⟩
    have : t = symmDiff s {i} := by rw [← hi, symmDiff_symmDiff_cancel_left]
    simp [this]


/-- Pairs of topes at distance `ℓ` are pairs (tope, `ℓ`-element set of hyperplanes). -/
def topeGen1Equiv (n ℓ : ℕ) (hl : 0 < ℓ) :
    Gen1 (topeGraph n) ℓ ≃ Finset (Fin n) × {e : Finset (Fin n) // e.card = ℓ} where
  toFun g := (g.1.1, ⟨symmDiff g.1.1 g.1.2, by rw [← topeGraph_dist]; exact g.2.2⟩)
  invFun p := ⟨(p.1, symmDiff p.1 p.2.1), by
      intro h
      have h2 := congrArg (fun t => symmDiff p.1 t) h
      simp only [symmDiff_self, symmDiff_symmDiff_cancel_left] at h2
      have hc := p.2.2
      rw [← h2] at hc
      simp at hc
      omega, by
      rw [topeGraph_dist, symmDiff_symmDiff_cancel_left]; exact p.2.2⟩
  left_inv g := by
    apply Subtype.ext
    simp [symmDiff_symmDiff_cancel_left]
  right_inv p := by
    ext
    · simp
    · simp [symmDiff_symmDiff_cancel_left]


/-- Degree-2 magnitude chains of length 2 of the tope graph are triples (tope, two
hyperplanes). -/
noncomputable def topeGen2Equiv (n : ℕ) :
    Finset (Fin n) × Fin n × Fin n ≃ Gen2 (topeGraph n) 2 := by
  apply Equiv.ofBijective (fun q =>
    (⟨(symmDiff q.1 {q.2.1}, q.1, symmDiff q.1 {q.2.2}), ?_, ?_, ?_⟩ : Gen2 (topeGraph n) 2))
  rotate_left
  · intro h
    have hc : (symmDiff (symmDiff q.1 {q.2.1}) q.1).card = 1 := by
      rw [symmDiff_comm, symmDiff_symmDiff_cancel_left]; simp
    rw [show (symmDiff q.1 {q.2.1}) = q.1 from h] at hc
    simp at hc
  · intro h
    have hc : (symmDiff q.1 (symmDiff q.1 {q.2.2})).card = 1 := by
      rw [symmDiff_symmDiff_cancel_left]; simp
    rw [show (symmDiff q.1 {q.2.2}) = q.1 from h.symm] at hc
    simp at hc
  · rw [topeGraph_dist, topeGraph_dist, symmDiff_comm (symmDiff q.1 {q.2.1}) q.1,
      symmDiff_symmDiff_cancel_left, symmDiff_symmDiff_cancel_left]
    simp
  constructor
  · rintro ⟨s, i, j⟩ ⟨s', i', j'⟩ h
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    subst h2
    have hi : ({i} : Finset (Fin n)) = {i'} := by
      have := congrArg (fun t => symmDiff s t) h1
      simpa [symmDiff_symmDiff_cancel_left] using this
    have hj : ({j} : Finset (Fin n)) = {j'} := by
      have := congrArg (fun t => symmDiff s t) h3
      simpa [symmDiff_symmDiff_cancel_left] using this
    simp_all
  · rintro ⟨⟨x, y, z⟩, hxy, hyz, hsum⟩
    dsimp only at hxy hyz hsum
    rw [topeGraph_dist, topeGraph_dist] at hsum
    have h1 : (symmDiff x y).card = 1 := by
      rcases Nat.eq_zero_or_pos (symmDiff x y).card with h | h
      · exact absurd (by simpa [symmDiff_eq_bot] using Finset.card_eq_zero.mp h) hxy
      · rcases Nat.eq_zero_or_pos (symmDiff y z).card with h' | h'
        · exact absurd (by simpa [symmDiff_eq_bot] using Finset.card_eq_zero.mp h') hyz
        · omega
    have h2 : (symmDiff y z).card = 1 := by
      rcases Nat.eq_zero_or_pos (symmDiff x y).card with h | h
      · exact absurd (by simpa [symmDiff_eq_bot] using Finset.card_eq_zero.mp h) hxy
      · omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h2
    refine ⟨(y, i, j), ?_⟩
    have hx : x = symmDiff y {i} := by
      rw [← hi, symmDiff_comm x y, symmDiff_symmDiff_cancel_left]
    have hz : z = symmDiff y {j} := by rw [← hj, symmDiff_symmDiff_cancel_left]
    simp [hx, hz]






end Application

/-! ## 6. The Coxeter group `(ℤ/2)ⁿ` and its Cayley graph -/

section Coxeter

/-- A graph isomorphism does not increase distances. -/
private lemma iso_dist_le {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (u v : V) : H.dist (e u) (e v) ≤ G.dist u v := by
  by_cases hr : G.Reachable u v
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    have := SimpleGraph.dist_le (p.map e.toHom)
    simpa [hp] using this
  · have h0 : G.dist u v = 0 := SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mpr (Or.inr hr)
    have hr' : ¬ H.Reachable (e u) (e v) := fun h => hr (by
      have := h.map e.symm.toHom
      simpa using this)
    rw [h0, SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mpr (Or.inr hr')]

/-- **Graph isomorphisms are isometries.** -/
theorem iso_dist_eq {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (u v : V) : H.dist (e u) (e v) = G.dist u v := by
  refine le_antisymm (iso_dist_le e u v) ?_
  have := iso_dist_le e.symm (e u) (e v)
  simpa using this

/-- Magnitude chain generators are transported along a graph isomorphism. -/
def genEquiv1 {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (ℓ : ℕ) :
    Gen1 G ℓ ≃ Gen1 H ℓ where
  toFun g := ⟨(e g.1.1, e g.1.2), by
      simpa using (e.toEquiv.injective.ne_iff).mpr g.2.1, by
      rw [iso_dist_eq]; exact g.2.2⟩
  invFun g := ⟨(e.symm g.1.1, e.symm g.1.2), by
      simpa using (e.symm.toEquiv.injective.ne_iff).mpr g.2.1, by
      rw [iso_dist_eq]; exact g.2.2⟩
  left_inv g := by
    apply Subtype.ext
    simp
  right_inv g := by
    apply Subtype.ext
    simp

variable {n : ℕ}

/-- The indicator function of a subset, viewed as an element of the Coxeter group
`(ℤ/2)ⁿ`. -/
def ind (s : Finset (Fin n)) : Fin n → ZMod 2 := fun j => if j ∈ s then 1 else 0

lemma ind_injective : Function.Injective (ind (n := n)) := by
  intro s t h
  ext j
  have hj := congrFun h j
  simp only [ind] at hj
  by_cases hs : j ∈ s <;> by_cases ht : j ∈ t <;> simp_all

lemma ind_surjective : Function.Surjective (ind (n := n)) := by
  have key : ∀ a : ZMod 2, a ≠ 1 → (0 : ZMod 2) = a := by decide
  intro f
  refine ⟨Finset.univ.filter (fun j => f j = 1), ?_⟩
  ext j
  simp only [ind, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : f j = 1
  · simp [h]
  · simp only [h, if_false]
    exact key _ h

/-- The indicator map turns symmetric difference into addition in `(ℤ/2)ⁿ`. -/
lemma ind_symmDiff (s t : Finset (Fin n)) : ind (symmDiff s t) = ind s + ind t := by
  ext j
  simp only [ind, Pi.add_apply, Finset.mem_symmDiff]
  by_cases hs : j ∈ s <;> by_cases ht : j ∈ t <;> simp [hs, ht]
  decide

lemma ind_singleton (i : Fin n) : ind ({i} : Finset (Fin n)) = Pi.single i 1 := by
  ext j
  simp only [ind, Finset.mem_singleton]
  by_cases h : j = i <;> simp [h, Pi.single_apply]

private lemma single_add_single (i : Fin n) :
    (Pi.single i 1 : Fin n → ZMod 2) + Pi.single i 1 = 0 := by
  ext j
  simp only [Pi.add_apply, Pi.single_apply, Pi.zero_apply]
  split_ifs with h <;> decide

/-- The **Cayley graph of the Coxeter group `(ℤ/2)ⁿ`** with respect to its `n` standard
Coxeter generators. -/
def cayleyGraph (n : ℕ) : SimpleGraph (Fin n → ZMod 2) where
  Adj u v := ∃ i, v = u + Pi.single i 1
  symm := by
    rintro u v ⟨i, rfl⟩
    exact ⟨i, by rw [add_assoc, single_add_single, add_zero]⟩
  loopless := by
    constructor
    rintro u ⟨i, hi⟩
    have := congrFun hi i
    simp only [Pi.add_apply, Pi.single_eq_same] at this
    exact absurd (left_eq_add.mp this) (by decide)

/-- **The tope graph of the coordinate arrangement is the Cayley graph of `(ℤ/2)ⁿ`.** -/
noncomputable def topeIsoCayley (n : ℕ) : topeGraph n ≃g cayleyGraph n where
  toEquiv := Equiv.ofBijective ind ⟨ind_injective, ind_surjective⟩
  map_rel_iff' := by
    intro s t
    show (∃ i, ind t = ind s + Pi.single i 1) ↔ (symmDiff s t).card = 1
    constructor
    · rintro ⟨i, hi⟩
      have ht : t = symmDiff s {i} := by
        apply ind_injective
        rw [ind_symmDiff, ind_singleton, hi]
      rw [ht, symmDiff_symmDiff_cancel_left]
      simp
    · intro h
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
      refine ⟨i, ?_⟩
      have ht : t = symmDiff s {i} := by rw [← hi, symmDiff_symmDiff_cancel_left]
      rw [ht, ind_symmDiff, ind_singleton]








end Coxeter

end MagnitudeTope


