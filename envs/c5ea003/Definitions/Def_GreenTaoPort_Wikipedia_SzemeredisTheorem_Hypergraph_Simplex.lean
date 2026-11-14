-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:50:42.670203+00:00
-- url     : https://prove2.me/theorems/1e6fcf94-3aff-4971-9f24-4b81f4451e98
-- title:
--   Weighted partite simplices and their AP-form realization
-- statement:
--   A dependent deleted-coordinate vector assigns a vertex to every part except one specified colour. A real-weighted partite simplex system assigns an edge weight to each such vector. The weight of a full labelled simplex is the product over all colours, and its normalized count is the mean of that product when all vertex parts are finite.
--
--   For cyclic vertex classes, the AP-simplex edge form at colour $j$ is $\sum_{i\ne j}(i-j)x_i$. The coordinate sum and first coordinate moment are supplied explicitly; they encode the progression difference with a minus sign and the initial term. Pulling a single real cyclic weight back through each AP-simplex form gives the corresponding weighted simplex system.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/Simplex.lean#L19-L137

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Partite weighted simplices

The dense and relative Szemerédi arguments are organized as counting lemmas
for a `(k-1)`-uniform, `k`-partite simplex.  An edge of colour `j` depends on
every vertex coordinate except `j`.  Keeping that dependency in the type
prevents accidental use of the omitted coordinate and matches the dependent
index used by the CFZ blow-up forms.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A vector with coordinate `j` deleted. -/
abbrev DeletedVector {k : ℕ} (V : Fin k → Type*) (j : Fin k) :=
  (i : {i : Fin k // i ≠ j}) → V i.1

/-- Delete coordinate `j` from a dependent vector. -/
def deleteCoordinate {k : ℕ} {V : Fin k → Type*}
    (x : (i : Fin k) → V i) (j : Fin k) :
    DeletedVector V j :=
  fun i => x i.1

/-- A weighted `(k-1)`-uniform, `k`-partite hypergraph. -/
structure WeightedSimplexSystem {k : ℕ} (V : Fin k → Type*) where
  edgeWeight : (j : Fin k) → DeletedVector V j → ℝ

namespace WeightedSimplexSystem

/-- Product of the `k` edge weights on a labelled simplex. -/
def simplexWeight {k : ℕ} {V : Fin k → Type*}
    (H : WeightedSimplexSystem V) (x : (i : Fin k) → V i) : ℝ :=
  ∏ j : Fin k, H.edgeWeight j (deleteCoordinate x j)

/-- Normalized count of labelled weighted simplices. -/
noncomputable def simplexCount {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)] (H : WeightedSimplexSystem V) : ℝ :=
  mean H.simplexWeight









end WeightedSimplexSystem

/-- The one-copy arithmetic-progression form attached to edge `j`. -/
def apSimplexForm (k N : ℕ) (j : Fin k)
    (x : DeletedVector (fun _ : Fin k => ZMod N) j) : ZMod N :=
  ∑ i : {i : Fin k // i ≠ j},
    (((i.1 : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x i

/-- Sum of all simplex coordinates.  It becomes the common difference,
up to sign, in the encoded progression. -/
def simplexCoordinateSum (k N : ℕ)
    (x : Fin k → ZMod N) : ZMod N :=
  ∑ i : Fin k, x i

/-- First moment of the simplex coordinates.  It becomes the initial term
of the encoded progression. -/
def simplexCoordinateMoment (k N : ℕ)
    (x : Fin k → ZMod N) : ZMod N :=
  ∑ i : Fin k, (i : ZMod N) * x i

/-- The edge form is the first moment minus `j` times the coordinate sum.
Consequently, the `k` edge values of one simplex form a cyclic arithmetic
progression. -/
theorem apSimplexForm_deleteCoordinate (k N : ℕ) (j : Fin k)
    (x : Fin k → ZMod N) :
    apSimplexForm k N j (deleteCoordinate x j) =
      simplexCoordinateMoment k N x -
        (j : ZMod N) * simplexCoordinateSum k N x := by
  classical
  let f : Fin k → ZMod N :=
    fun i => (((i : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x i
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype (fun i : Fin k => i ≠ j) f
  have hcomplement :
      (∑ i : {i : Fin k // ¬i ≠ j}, f i.1) = 0 := by
    apply Finset.sum_eq_zero
    intro i
    simp only [Finset.mem_univ, forall_const]
    have hij : i.1 = j := not_ne_iff.mp i.2
    rw [hij]
    simp [f]
  have hsum : (∑ i : {i : Fin k // i ≠ j}, f i.1) = ∑ i : Fin k, f i := by
    rw [hcomplement, add_zero] at hsplit
    exact hsplit
  rw [apSimplexForm]
  change (∑ i : {i : Fin k // i ≠ j}, f i.1) =
    simplexCoordinateMoment k N x -
      (j : ZMod N) * simplexCoordinateSum k N x
  rw [hsum]
  simp only [simplexCoordinateMoment, simplexCoordinateSum, f]
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- The weighted simplex system whose simplices encode arithmetic
progressions. -/
def apSimplexSystem (k N : ℕ) (f : ZMod N → ℝ) :
    WeightedSimplexSystem (fun _ : Fin k => ZMod N) where
  edgeWeight j x := f (apSimplexForm k N j x)



end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.WeightedSimplexSystem.ctorIdx,
    `Wikipedia.SzemeredisTheorem.WeightedSimplexSystem.mk.inj,
    `Wikipedia.SzemeredisTheorem.WeightedSimplexSystem.mk.injEq,
    `Wikipedia.SzemeredisTheorem.WeightedSimplexSystem.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.WeightedSimplexSystem.noConfusionType,
    `Wikipedia.SzemeredisTheorem.apSimplexForm.eq_1,
    `Wikipedia.SzemeredisTheorem.simplexCoordinateMoment.eq_1,
    `Wikipedia.SzemeredisTheorem.simplexCoordinateSum.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


