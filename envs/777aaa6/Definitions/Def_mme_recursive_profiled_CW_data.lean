-- Prove2me | Definitions.Def_mme_recursive_profiled_CW_data
-- name    : mme_recursive_profiled_CW_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-13T14:41:58.934684+00:00
-- url     : https://prove2.me/theorems/6f1163d7-4ba1-4040-8099-812ca02b670e
-- title:
--   Finite level-descending CW profile recipes with full copy costs
-- statement:
--   Actual CW5 powers are projected by predicates on their complete flat grade words. An exact extraction step stores finite hash selections, profiles and all-mode hole budgets, with no tensor restriction or isomorphism field. Boundary endpoints contain the concrete complementary profiles and factorial/power-of-five matrix dimensions. A recursive plan descends strictly in level, covers a tolerated interface by finitely many exact profile cases, and recursively multiplies the input-copy overhead and the output-copy gain. Soundness is a separate theorem; the definition does not assert existence of a successful numerical plan.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 , Theorems 6.2 and 6.4, Proposition 6.3. Finite constructive certificate interface with explicit type-cover source costs.

import Definitions.Def_mme_recursive_yz_stage_certificate
import Definitions.Def_mme_recursive_yz_boundary_data
import Definitions.Def_mme_recursive_yz_cell_partition

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Certificate Module
open scoped Classical
set_option autoImplicit false
universe u

namespace MME.ProfiledCW

/-- The same literal elementary CW positions at every recursive level. -/
abbrev FineWord (N : ℕ) := Fin N → Fin 3
abbrev Predicate (N : ℕ) := Fin 3 → FineWord N → Prop
abbrev Coordinate (N : ℕ) := Fin N → ULift.{u} (Fin 7)

def fine {N : ℕ} (x : Coordinate.{u} N) : FineWord N :=
  fun r ↦ MME.cwSquareCoordGrade 5 (x r).down

noncomputable def raw (K : Type u) [Field K] (N : ℕ) : TensorObj K 3 :=
  (CWObj K 5).kronPow N

noncomputable def canonical (K : Type u) [Field K] (N : ℕ) (i : Fin 3) :
    Basis (Coordinate.{u} N) K ((raw K N).V i) :=
  kronPowModeWordBasis (CWObj K 5) i
    ((MME.DWZStep1Support.cwThreeCanonicalBasis K 5 i).reindex Equiv.ulift.symm) N

/-- An actual all-mode projection of CW5^N. The predicate can describe exact
types or a tolerance band containing many exact types. -/
noncomputable def tensor (K : Type u) [Field K] {N : ℕ} (P : Predicate N) : TensorObj K 3 :=
  (raw K N).basisAllAllowedSubtensor (canonical K N) (fun i x ↦ P i (fine x))

def supported {N : ℕ} (x : Fin 3 → FineWord N) : Prop :=
  ∀ r, (x 0 r).val + (x 1 r).val + (x 2 r).val = 2

/-- Reinterpret a flat word in a chosen finite family of equal-length blocks. -/
def split {P : Type} {ell L N : ℕ} (positions : Fin L ≃ P)
    (length : L * 2 ^ (ell - 1) = N) (x : FineWord N) : P → CompleteWord ell :=
  fun p r ↦ x (Fin.cast length (finProdFinEquiv (positions.symm p, r)))

def flatten {P : Type} {ell L N : ℕ} (positions : Fin L ≃ P)
    (length : L * 2 ^ (ell - 1) = N) (x : P → CompleteWord ell) : FineWord N :=
  fun r ↦ let p := finProdFinEquiv.symm (Fin.cast length.symm r)
    x (positions p.1) p.2

/-- All data of one exact-profile extraction. Its hypotheses concern finite
word sets and hashes; there is no assumed tensor restriction. -/
structure ExactStep (ell N : ℕ) (P : Predicate N) where
  hash : HashExtraction.HashData
  stage : Stage hash
  level : stage.ell = ell
  length : stage.L * 2 ^ (stage.ell - 1) = N
  count : ℕ
  state : hash.State
  address : Fin count → hash.Edge
  injective : Function.Injective address
  target : ∀ j, address j ∈ RecursiveXHash.target hash.m
  bucketed : ∀ j, address j ∈ RecursiveXHash.bucketed hash.m hash.positions
    (hash.labels.image (fun a : ℕ ↦ (a : ZMod hash.p))) state
  hashed : ∀ j, address j ∈ RecursiveXHash.hashed hash.m hash.positions
    (hash.labels.image (fun a : ℕ ↦ (a : ZMod hash.p))) state
  isolated : ∀ j b, b ∈ RecursiveXHash.bucketed hash.m hash.positions
      (hash.labels.image (fun a : ℕ ↦ (a : ZMod hash.p))) state →
    RecursiveXHash.block 0 (address j) = RecursiveXHash.block 0 b → address j = b
  holes : ∀ j (i : Fin 3), 4 * stage.repairScale *
    ((unbrokenWords stage.total i (address j) (stage.mu i)).filter
        (fun f ↦ ¬ P i (flatten stage.positions length f)) ∪
      (if i = 1 then filterHoles stage.total hash.m hash.positions
          (hash.labels.image (fun a : ℕ ↦ (a : ZMod hash.p))) state 0
          (stage.mu 1) (address j) (stage.keep 0 (address j))
       else if i = 2 then filterHoles stage.total hash.m hash.positions
          (hash.labels.image (fun a : ℕ ↦ (a : ZMod hash.p))) state 1
          (stage.mu 2) (address j) (stage.keep 1 (address j))
       else ∅)).card ≤ (unbrokenWords stage.total i (address j) (stage.mu i)).card

def ExactStep.copies {ell N : ℕ} {P : Predicate N} (E : ExactStep ell N P) : ℕ :=
  E.count / 8 ^ E.stage.repairExponent

def ExactStep.output {ell N : ℕ} {P : Predicate N} (E : ExactStep ell N P) : Predicate N :=
  fun i x ↦
    Graded E.stage.total i E.stage.reference (split E.stage.positions E.length x) ∧
      Useful (fullCell E.stage.total E.stage.reference) (E.stage.mu i)
        (split E.stage.positions E.length x)

/-- A terminal interface is covered by concrete complementary boundary
profiles, with the full matrix dimensions from their exact finite counts. -/
structure BoundaryEnd (ell N : ℕ) (P : Predicate N) where
  L : ℕ
  cells : ℕ
  length : L * 2 ^ (ell - 1) = N
  cell : Fin L → Fin cells
  shape : Fin cells → Fin 3 → ℕ
  mu : Fin 3 → Fin cells → CompleteWord ell → ℕ
  partition : Partition cell
  profile : ∀ j, Boundary.Profile ell (partition.size j)
  zeroMode : Fin partition.parts → Fin 3
  shapes : ∀ j, shape (partition.cells j) = (profile j).shape (zeroMode j)
  profiles : ∀ j i, mu i (partition.cells j) = (profile j).mu (zeroMode j) i
  inside : ∀ i x,
    ((∀ p, CWCells.grade (split (Equiv.refl (Fin L)) length x p) = shape (cell p) i) ∧
      Useful cell (mu i) (split (Equiv.refl (Fin L)) length x)) → P i x

def BoundaryEnd.a {ell N : ℕ} {P : Predicate N} (B : BoundaryEnd ell N P) : ℕ :=
  ∏ j, (B.profile j).a (B.zeroMode j)
def BoundaryEnd.b {ell N : ℕ} {P : Predicate N} (B : BoundaryEnd ell N P) : ℕ :=
  ∏ j, (B.profile j).b (B.zeroMode j)
def BoundaryEnd.c {ell N : ℕ} {P : Predicate N} (B : BoundaryEnd ell N P) : ℕ :=
  ∏ j, (B.profile j).c (B.zeroMode j)

/-- A finite, strictly level-descending recipe on actual CW projections.
One source copy is charged for each exact type case. The common output
copy count is retained in every subsequent recursion step. -/
inductive Plan (N : ℕ) : (ell : ℕ) → Predicate N → Type
  | boundary {ell P} (data : BoundaryEnd ell N P) : Plan N ell P
  | descend {ell lower : ℕ} {P Q : Predicate N}
      (level_decreases : lower < ell)
      (types copies : ℕ)
      (steps : Fin types → ExactStep lower N P)
      (enough : ∀ j, copies ≤ (steps j).copies)
      (inside : ∀ j i x, (steps j).output i x → Q i x)
      (cover : ∀ x : Fin 3 → FineWord N, supported x → (∀ i, Q i (x i)) →
        ∃! j, ∀ i, (steps j).output i (x i))
      (next : Plan N lower Q) : Plan N ell P

def Plan.inputs {N ell : ℕ} {P : Predicate N} : Plan N ell P → ℕ
  | .boundary _ => 1
  | .descend _ types _ _ _ _ _ next => types * next.inputs
def Plan.outputs {N ell : ℕ} {P : Predicate N} : Plan N ell P → ℕ
  | .boundary _ => 1
  | .descend _ _ copies _ _ _ _ next => copies * next.outputs
def Plan.a {N ell : ℕ} {P : Predicate N} : Plan N ell P → ℕ
  | .boundary B => B.a
  | .descend _ _ _ _ _ _ _ next => next.a
def Plan.b {N ell : ℕ} {P : Predicate N} : Plan N ell P → ℕ
  | .boundary B => B.b
  | .descend _ _ _ _ _ _ _ next => next.b
def Plan.c {N ell : ℕ} {P : Predicate N} : Plan N ell P → ℕ
  | .boundary B => B.c
  | .descend _ _ _ _ _ _ _ next => next.c

end MME.ProfiledCW


