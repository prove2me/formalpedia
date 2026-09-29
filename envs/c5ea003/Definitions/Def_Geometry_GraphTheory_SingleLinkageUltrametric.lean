-- Prove2me | Definitions.Def_Geometry_GraphTheory_SingleLinkageUltrametric
-- name    : Geometry_GraphTheory_SingleLinkageUltrametric
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:17:13.077893+00:00
-- url     : https://prove2.me/theorems/3d821bda-12bf-4387-af7f-8d480752f99b
-- title:
--   Aether Catalog definitions — Geometry_GraphTheory_SingleLinkageUltrametric
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.GraphTheory.SingleLinkageUltrametric`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/GraphTheory/SingleLinkageUltrametric.lean by skeleton subtraction
import Mathlib

/-!
# The single-linkage ultrametric from finite Rips graph filtrations

For a finite type `α` equipped with a dissimilarity function `d : α → α → ℝ`, we
build the *Rips graph* `ripsGraphOf d ε` at scale `ε`, in which two distinct
points are adjacent when at least one of the two directed dissimilarities is at
most `ε`.  Two points are *connected at scale `ε`*, written `ConnAt d ε x y`,
when they are reachable in this graph.

The single-linkage threshold `connThreshold d x y` is the least scale (among the
finitely many relevant candidate scales) at which `x` and `y` become connected.
We prove that this threshold satisfies the strong (ultrametric) triangle
inequality

`connThreshold d x y ≤ max (connThreshold d x z) (connThreshold d z y)`

together with symmetry, the upper bound by the direct dissimilarity, and the
reflexive `connThreshold d x x = 0` (under nonnegativity of `d`).

The development is finite-combinatorial throughout: the candidate scales form a
`Finset` (`0` together with all values `d a b`), and the threshold is the `min'`
of the nonempty subset of candidate scales at which the points are connected.

The instance `[DecidableEq α]` is kept as part of the requested finite setting;
it turns out to be unnecessary for the mathematics below (only `[Fintype α]` is
used, with decidability of the predicates on `ℝ` supplied classically), so it is
explicitly `omit`-ted from the individual statements that do not need it.
-/

open scoped Classical

namespace SingleLinkage

/-! ## The Rips graph and connectivity at a scale -/

variable {α : Type*}

/-- The Rips graph of `d` at scale `ε`: distinct points are adjacent when one of
the two directed dissimilarities is at most `ε`. -/
def ripsGraphOf (d : α → α → ℝ) (ε : ℝ) : SimpleGraph α where
  Adj x y := x ≠ y ∧ (d x y ≤ ε ∨ d y x ≤ ε)
  symm := by
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h2 | h2
    · exact Or.inr h2
    · exact Or.inl h2
  loopless := ⟨fun x h => h.1 rfl⟩

/-- `x` and `y` are connected at scale `ε` when they are reachable in the Rips
graph at scale `ε`. -/
def ConnAt (d : α → α → ℝ) (ε : ℝ) (x y : α) : Prop :=
  (ripsGraphOf d ε).Reachable x y



/-- Every point is connected to itself at every scale. -/
theorem ConnAt.refl (d : α → α → ℝ) (ε : ℝ) (x : α) : ConnAt d ε x x :=
  SimpleGraph.Reachable.refl x




/-- A single edge connects distinct points at scale `d x y`. -/
theorem ConnAt.of_ne (d : α → α → ℝ) {x y : α} (h : x ≠ y) :
    ConnAt d (d x y) x y :=
  SimpleGraph.Adj.reachable ⟨h, Or.inl le_rfl⟩

/-- Any two points are connected at scale `d x y`. -/
theorem ConnAt.of_dist (d : α → α → ℝ) (x y : α) : ConnAt d (d x y) x y := by
  by_cases h : x = y
  · subst h; exact ConnAt.refl d (d x x) x
  · exact ConnAt.of_ne d h

/-! ## Candidate scales and the connectivity threshold -/

variable [Fintype α] [DecidableEq α]

/-- The finite set of candidate scales: `0` together with all values `d a b`. -/
noncomputable def scales (d : α → α → ℝ) : Finset ℝ :=
  insert 0 (Finset.image (fun p : α × α => d p.1 p.2) Finset.univ)


omit [DecidableEq α] in
/-- Every dissimilarity value is a candidate scale. -/
theorem dist_mem_scales (d : α → α → ℝ) (x y : α) : d x y ∈ scales d :=
  Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(x, y), Finset.mem_univ _, rfl⟩)

/-- The candidate scales at which `x` and `y` are connected. -/
noncomputable def connScales (d : α → α → ℝ) (x y : α) : Finset ℝ :=
  (scales d).filter (fun ε => ConnAt d ε x y)

omit [DecidableEq α] in
theorem mem_connScales {d : α → α → ℝ} {x y : α} {ε : ℝ} :
    ε ∈ connScales d x y ↔ ε ∈ scales d ∧ ConnAt d ε x y := by
  simp [connScales]

omit [DecidableEq α] in
/-- The set of connecting candidate scales is nonempty. -/
theorem connScales_nonempty (d : α → α → ℝ) (x y : α) :
    (connScales d x y).Nonempty :=
  ⟨d x y, mem_connScales.mpr ⟨dist_mem_scales d x y, ConnAt.of_dist d x y⟩⟩

/-- The single-linkage connectivity threshold: the least candidate scale at
which `x` and `y` are connected. -/
noncomputable def connThreshold (d : α → α → ℝ) (x y : α) : ℝ :=
  (connScales d x y).min' (connScales_nonempty d x y)









end SingleLinkage


