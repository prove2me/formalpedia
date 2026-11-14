-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:49:51.820232+00:00
-- url     : https://prove2.me/theorems/ab1827ac-7e28-4214-b3f9-779db68bded5
-- title:
--   Complete ordered partite patterns and per-face removal
-- statement:
--   An ordered face of arity $r$ among $k$ labelled parts is an increasing embedding of the coordinate indices. Restricting a full tuple gives its face tuple; explicit equivalences split the full coordinates into the face and its complement.
--
--   A weighted ordered pattern assigns a real function to every ordered $r$-face. Its full-tuple weight is the product of all face weights, and its count is their normalized mean on a finite vertex type. Predicate-valued patterns give zero–one weights and a finite set of labelled occurrences.
--
--   A deletion family chooses a finite set on each ordered face, and a cover meets every original occurrence. The uniform removal predicate asks, for each $\varepsilon>0$, for a positive count threshold independent of the nonempty finite vertex type such that low-count patterns have a cover of deletion density at most $\varepsilon$ on every face separately.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedPattern.lean#L20-L386

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Complete ordered partite hypergraph patterns

Recursive hypergraph removal naturally produces lower-rank constraints on a
fixed collection of vertex classes.  It is convenient to index an ordered
rank-`r` face by an embedding `Fin r ↪ Fin k`.  This permits composition of
faces without quotienting by permutations.

This file defines weighted and unweighted complete ordered patterns, their
normalized occurrence counts, deletions, and the uniform removal property
used by the rank induction.  Rank zero is proved directly.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The increasing rank-`r` face among `k` vertex classes with a specified
canonical order. -/
abbrev OrderedFace (k r : ℕ) :=
  Fin r ↪o Fin k

instance orderedFaceDecidableEq
    (k r : ℕ) : DecidableEq (OrderedFace k r) :=
  Function.Injective.decidableEq
    (f := fun e : OrderedFace k r => (e : Fin r → Fin k))
    DFunLike.coe_injective

/-- Restrict a full labelled tuple along an ordered face. -/
def orderedFaceTuple
    {G : Type*} {k r : ℕ}
    (e : OrderedFace k r) (x : Fin k → G) :
    Fin r → G :=
  fun i => x (e i)

/-- Vertex coordinates outside an ordered face. -/
abbrev OrderedFaceComplement
    {k r : ℕ} (e : OrderedFace k r) :=
  {v : Fin k // v ∉ Set.range e}

/-- Split the full vertex index into an ordered face and its complement. -/
noncomputable def orderedFaceSumEquiv
    {k r : ℕ} (e : OrderedFace k r) :
    Fin r ⊕ OrderedFaceComplement e ≃ Fin k :=
  (Equiv.sumCongr e.toEmbedding.toEquivRange
      (Equiv.refl (OrderedFaceComplement e))).trans
    (Equiv.sumCompl
      (fun v : Fin k => v ∈ Set.range e))

/-- Split a full tuple into its values on an ordered face and on the
complementary vertex coordinates. -/
noncomputable def splitOrderedFaceEquiv
    {G : Type*} {k r : ℕ} (e : OrderedFace k r) :
    (Fin k → G) ≃
      ((Fin r → G) × (OrderedFaceComplement e → G)) :=
  (Equiv.piCongrLeft (fun _ : Fin k => G)
      (orderedFaceSumEquiv e)).symm.trans
    (Equiv.sumPiEquivProdPi
      (fun _ : Fin r ⊕ OrderedFaceComplement e => G))



/-- Restrict a full tuple to the complementary vertex coordinates. -/
def orderedFaceComplementTuple
    {G : Type*} {k r : ℕ}
    (e : OrderedFace k r) (x : Fin k → G) :
    OrderedFaceComplement e → G :=
  fun v => x v.1















/-- A weighted complete ordered rank-`r` pattern. -/
structure WeightedOrderedPattern
    (G : Type*) (k r : ℕ) where
  edgeWeight : OrderedFace k r → (Fin r → G) → ℝ

namespace WeightedOrderedPattern

/-- Product of all ordered face weights on a labelled full tuple. -/
noncomputable def patternWeight
    {G : Type*} {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (x : Fin k → G) : ℝ :=
  ∏ e : OrderedFace k r,
    H.edgeWeight e (orderedFaceTuple e x)

/-- Normalized density of labelled pattern occurrences. -/
noncomputable def patternCount
    {G : Type*} [Fintype G] {k r : ℕ}
    (H : WeightedOrderedPattern G k r) : ℝ :=
  mean H.patternWeight







end WeightedOrderedPattern

/-- A predicate-valued complete ordered rank-`r` pattern. -/
structure OrderedPattern
    (G : Type*) (k r : ℕ) where
  edge : OrderedFace k r → (Fin r → G) → Prop

namespace OrderedPattern

/-- A labelled full tuple satisfies every ordered edge predicate. -/
def IsOccurrence
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r)
    (x : Fin k → G) : Prop :=
  ∀ e, H.edge e (orderedFaceTuple e x)

/-- The finite set of labelled occurrences. -/
noncomputable def occurrenceFinset
    {G : Type*} [Fintype G] [DecidableEq G] {k r : ℕ}
    (H : OrderedPattern G k r) :
    Finset (Fin k → G) := by
  classical
  exact Finset.univ.filter H.IsOccurrence



/-- Regard predicates as zero-one edge weights. -/
noncomputable def toWeighted
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r) :
    WeightedOrderedPattern G k r := by
  classical
  exact
    { edgeWeight := fun e y =>
        if H.edge e y then 1 else 0 }













/-- One deleted rank-`r` face set for every ordered face. -/
abbrev DeletionFamily
    {G : Type*} [DecidableEq G] (k r : ℕ) :=
  (e : OrderedFace k r) → Finset (Fin r → G)

/-- Every original occurrence meets at least one deleted ordered face. -/
def IsCover
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    (D : DeletionFamily (G := G) k r) : Prop :=
  ∀ x, x ∈ H.occurrenceFinset →
    ∃ e, orderedFaceTuple e x ∈ D e

/-- Normalized density of the deletion in one ordered face. -/
noncomputable def faceDeletionDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k r)
    (e : OrderedFace k r) : ℝ :=
  (D e).card / Fintype.card (Fin r → G)





end OrderedPattern

/-- Uniform per-ordered-face removal for complete ordered rank-`r`
patterns on `k` equal finite vertex classes. -/
def HasUniformOrderedPatternRemoval (k r : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧
      ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G],
        ∀ H : OrderedPattern G k r,
          H.toWeighted.patternCount < c →
            ∃ D : OrderedPattern.DeletionFamily
                (G := G) k r,
              H.IsCover D ∧
                ∀ e, OrderedPattern.faceDeletionDensity D e ≤ ε





end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.OrderedPattern.ctorIdx,
    `Wikipedia.SzemeredisTheorem.OrderedPattern.faceDeletionDensity.eq_1,
    `Wikipedia.SzemeredisTheorem.OrderedPattern.mk.inj,
    `Wikipedia.SzemeredisTheorem.OrderedPattern.mk.injEq,
    `Wikipedia.SzemeredisTheorem.OrderedPattern.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.OrderedPattern.noConfusionType,
    `Wikipedia.SzemeredisTheorem.OrderedPattern.occurrenceFinset.eq_1,
    `Wikipedia.SzemeredisTheorem.OrderedPattern.toWeighted.eq_1,
    `Wikipedia.SzemeredisTheorem.WeightedOrderedPattern.ctorIdx,
    `Wikipedia.SzemeredisTheorem.WeightedOrderedPattern.mk.inj,
    `Wikipedia.SzemeredisTheorem.WeightedOrderedPattern.mk.injEq,
    `Wikipedia.SzemeredisTheorem.WeightedOrderedPattern.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.WeightedOrderedPattern.noConfusionType,
    `Wikipedia.SzemeredisTheorem.WeightedOrderedPattern.patternCount.eq_1,
    `Wikipedia.SzemeredisTheorem.orderedFaceComplementTuple.eq_1,
    `Wikipedia.SzemeredisTheorem.orderedFaceSumEquiv.eq_1,
    `Wikipedia.SzemeredisTheorem.orderedFaceTuple.eq_1,
    `Wikipedia.SzemeredisTheorem.splitOrderedFaceEquiv.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


