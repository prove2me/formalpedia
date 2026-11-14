-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:51:21.34697+00:00
-- url     : https://prove2.me/theorems/eb8c4198-7f54-40c8-9a4c-2727ab04b85a
-- title:
--   Bernoulli expansion of bounded deleted-coordinate tests
-- statement:
--   For real parameters $(p_i)$ and a Boolean assignment $b$, the product Bernoulli weight is
--
--   $$
--   \prod_i\begin{cases}p_i,&b_i=1,\\1-p_i,&b_i=0.\end{cases}
--   $$
--
--   The cut-coordinate type pairs a colour with a deleted-coordinate tuple. Boolean assignments on this type give zero–one cut-test families; conversely a real cut-test family is flattened into its scalar coordinates. A full tuple embeds its used cut coordinates by retaining the colour label. The bundle also supplies the generalized convolution of a Boolean assignment. The Bernoulli formula is defined for arbitrary real parameters; its probability interpretation uses parameters in $[0,1]$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/BooleanCutReduction.lean#L20-L295

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Reduction of bounded cut tests to Boolean cut tests

On a finite space, a `[0,1]`-valued cut-test family is a convex mixture of
its Boolean vertices.  Since every monomial in a cut correlation uses each
test coordinate at most once, the correlation is exactly the same convex
mixture of Boolean correlations.  Consequently it is enough to control the
finite family of Boolean cut tests in the dense-model theorem.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial

/-! ## Finite Bernoulli mixtures -/

/-- Product Bernoulli weight of a Boolean assignment. -/
def bernoulliAssignmentWeight
    {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (b : κ → Bool) : ℝ :=
  ∏ i, if b i then p i else 1 - p i

/-- Real indicator of one bit of an assignment. -/
def booleanValue {κ : Type*} (b : κ → Bool) (i : κ) : ℝ :=
  if b i then 1 else 0









/-! ## Boolean cut coordinates -/

/-- One scalar coordinate in a cut-test family. -/
abbrev CutTestCoordinate (G : Type*) (r : ℕ) :=
  Fin r × (Fin (r - 1) → G)

/-- A Boolean choice for every scalar coordinate of a cut-test family. -/
abbrev BooleanCutAssignment (G : Type*) (r : ℕ) :=
  CutTestCoordinate G r → Bool

/-- Regard a Boolean assignment as a `{0,1}`-valued cut-test family. -/
def cutTestFamilyOfBooleanAssignment
    {G : Type*} {r : ℕ}
    (b : BooleanCutAssignment G r) :
    CutTestFamily G r :=
  fun i y => booleanValue b ⟨i, y⟩



/-- Flatten a cut-test family to its finite vector of scalar coordinates. -/
def cutTestCoordinateValue
    {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) :
    CutTestCoordinate G r → ℝ :=
  fun q => u q.1 q.2

/-- The coordinates selected by one full tuple, as an embedding indexed by
the edge colour.  Injectivity is immediate from the colour component. -/
def usedCutTestCoordinateEmbedding
    {G : Type*} {r : ℕ} (x : Fin r → G) :
    Fin r ↪ CutTestCoordinate G r where
  toFun i := ⟨i, eraseCoordinate i x⟩
  inj' := by
    intro i j h
    exact congrArg Prod.fst h









/-! ## The finite dense-model test family -/

/-- Generalized convolution belonging to one Boolean cut assignment. -/
noncomputable def booleanCutConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (b : BooleanCutAssignment G r) : G → ℝ :=
  generalizedConvolution r
    (cutTestFamilyOfBooleanAssignment b)













end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.bernoulliAssignmentWeight.eq_1,
    `Wikipedia.SzemeredisTheorem.cutTestCoordinateValue.eq_1,
    `Wikipedia.SzemeredisTheorem.cutTestFamilyOfBooleanAssignment.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


