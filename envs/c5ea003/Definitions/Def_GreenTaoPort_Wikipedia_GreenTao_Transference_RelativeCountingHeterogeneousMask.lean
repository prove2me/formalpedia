-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingHeterogeneousMask
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingHeterogeneousMask
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:13:37.813647+00:00
-- url     : https://prove2.me/theorems/72c7039e-09e2-4638-bf4b-26d532e96b15
-- title:
--   Independent masks on the two copies of a counting system
-- statement:
--   For two Boolean copies of an AP system, the active mask may depend on both the copy and face. This bundle defines the copy-dependent majorants and the corresponding majorized cut system, whose factors are required to be nonnegative and dominated on every nondistinguished face. At a paid or terminal cube vertex, the distinguished Boolean coordinate determines which copy’s mask controls selection. Two special masks represent the sparse-dense and dense-sparse orientations.
--
--   Arbitrary weighted simplex systems are handled by reconstructing their two-copy cut tests and centered correlations, and packaging them in a majorized cut system below these independent AP majorants. The construction of correlations assumes $N
--   e0$; the algebraic systems and masks themselves allow any natural modulus.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/RelativeCountingHeterogeneousMask.lean#L30-L1540

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoderTerminal
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Copy-dependent masks in relative counting

The two copies in a projected relative-counting correlation need not have
the same majorant.  This file allows a separate active-face mask

`active : Bool → Fin (n + 1) → Bool`

for each copy.  The corresponding Cauchy--Schwarz stage selector reads the
copy from the distinguished Boolean coordinate of a face vertex.  Thus a
face can retain the `false` copy of `ν`, the `true` copy, both copies, or
neither copy independently.

The stable stage and terminal decoders then give a full structural CFZ
certificate and the usual quantitative root bound.  The final specialization
uses `ν` on the `false` copy and the constant majorant one on the `true`
copy, which is the cross-copy case required by relative counting.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## The copy-dependent AP cut system -/

/-- Copy-dependent AP face majorants. -/
def apCopyMaskedFaceMajorant
    {k N : ℕ}
    (ν : ZMod N → ℝ)
    (active : Bool → Fin k → Bool)
    (b : Bool) :
    Fin k → ZMod N → ℝ :=
  apMaskedFaceMajorant ν (active b)



/-- The exact two-copy cut system with an independent active mask on each
copy. -/
noncomputable def apTwoCopyHeterogeneousMaskedMajorizedCutSystem
    (n N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Bool → Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j) :
    MajorizedCutSystem
      (Bool → ZMod N) (ZMod N) n where
  core := fun _ y => apFaceCenteredCore n N ν j y
  factor := fun a => apTwoCopyCutTest n N g j a
  majorant := fun a =>
    apTwoCopyCutTest n N
      (apCopyMaskedFaceMajorant ν active) j a
  factor_nonneg := fun a t z =>
    (apTwoCopyCutTest_mono n N g
      (apCopyMaskedFaceMajorant ν active)
      j (fun b t z => hrest b t z) a t z).1
  factor_le_majorant := fun a t z =>
    (apTwoCopyCutTest_mono n N g
      (apCopyMaskedFaceMajorant ν active)
      j (fun b t z => hrest b t z) a t z).2



/-! ## Copy-aware recursive stage selectors -/

/-- At a paid Cauchy--Schwarz face, select a generated Boolean vertex
exactly when the copy read from its distinguished coordinate is active on
that face. -/
noncomputable def apCSHeterogeneousOrderedStageFaceExponent
    (r s : ℕ)
    (active :
      Bool → Fin (((s + 1) + r) + 1) → Bool)
    (j : Fin (((s + 1) + r) + 1)) :
    LinearFormsExponent (((s + 1) + r) + 1) :=
  faceLinearFormsExponent
    (apCSOrderedStageCurrentFace r s j)
    (fun ω =>
      if ∃ bits : Fin (r + 1) → Bool,
          apCSOrderedStageVertex r s j bits = ω
      then
        active
          (ω (apCSOrderedStageDistinguishedVertexIndex
            r s j))
          (apCSOrderedStageCurrentFace r s j)
      else false)



/-! ## Copy-aware paid stage moments -/









/-! ## Copy-aware terminal selector -/

/-- At the terminal cube, a non-distinguished face vertex is selected
exactly when its value at the distinguished coordinate chooses an active
copy for that face. -/
def apCSHeterogeneousTerminalExponent
    {k : ℕ}
    (active : Bool → Fin k → Bool)
    (j : Fin k) :
    LinearFormsExponent k :=
  fun i ω =>
    if hij : i = j then false
    else active (ω ⟨j, fun h => hij h.symm⟩) i





namespace MajorizedCutSystem

















end MajorizedCutSystem

/-! ## Quantitative correlation bounds -/



/-- Mask with the `false` copy sparse and the `true` copy already bounded
by one. -/
def apFalseSparseTrueDenseMask
    {k : ℕ} (active : Fin k → Bool) :
    Bool → Fin k → Bool :=
  fun b i => if b then false else active i







/-- Mask with the `true` copy sparse and the `false` copy bounded by one. -/
def apFalseDenseTrueSparseMask
    {k : ℕ} (active : Fin k → Bool) :
    Bool → Fin k → Bool :=
  fun b i => if b then active i else false







/-! ## Arbitrary weighted-simplex factors -/

namespace MajorizedCutSystem



end MajorizedCutSystem

/-- Reconstruct the two-copy cut factor of an arbitrary pair of weighted
simplex systems.  The name is intentionally leaf-specific so this module
can be imported by `RelativeCountingInduction` without a declaration
cycle. -/
def heterogeneousMaskSimplexTwoCopyCutTest
    (n N : ℕ)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (a : Bool → ZMod N) :
    CutTestFamily (ZMod N) n := by
  cases n with
  | zero =>
      exact fun t => Fin.elim0 t
  | succ m =>
      exact fun t z =>
        ∏ b : Bool,
          (H b).edgeWeight (j.succAbove t)
            (deleteCoordinate
              (Fin.insertNth j (a b)
                (Fin.insertNth t 0 z))
              (j.succAbove t))





theorem heterogeneousMaskSimplexTwoCopyCutTest_mono
    (n N : ℕ)
    (H K : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (hHK :
      ∀ b t x,
        0 ≤ (H b).edgeWeight (j.succAbove t) x ∧
          (H b).edgeWeight (j.succAbove t) x ≤
            (K b).edgeWeight (j.succAbove t) x)
    (a : Bool → ZMod N)
    (t : Fin n) (z : Fin (n - 1) → ZMod N) :
    0 ≤ heterogeneousMaskSimplexTwoCopyCutTest
        n N H j a t z ∧
      heterogeneousMaskSimplexTwoCopyCutTest
          n N H j a t z ≤
        heterogeneousMaskSimplexTwoCopyCutTest
          n N K j a t z := by
  cases n with
  | zero =>
      exact Fin.elim0 t
  | succ m =>
      constructor
      · unfold heterogeneousMaskSimplexTwoCopyCutTest
        exact Finset.prod_nonneg fun b _ =>
          (hHK b t _).1
      · unfold heterogeneousMaskSimplexTwoCopyCutTest
        exact Finset.prod_le_prod
          (fun b _ => (hHK b t _).1)
          (fun b _ => (hHK b t _).2)

theorem heterogeneousMaskSimplexTwoCopyCutTest_apHeterogeneous
    (n N : ℕ)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (t : Fin n) (z : Fin (n - 1) → ZMod N) :
    heterogeneousMaskSimplexTwoCopyCutTest n N
        (fun b => apHeterogeneousSimplexSystem n N (g b))
        j a t z =
      apTwoCopyCutTest n N g j a t z := by
  cases n with
  | zero => exact Fin.elim0 t
  | succ m => rfl

/-- Centered two-copy correlation for arbitrary weighted-simplex factors. -/
noncomputable def heterogeneousMaskSimplexTwoCopyCenteredCorrelation
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1)) : ℝ :=
  mean₂ fun a : Bool → ZMod N =>
    fun y : Fin n → ZMod N =>
      apFaceCenteredCore n N ν j y *
        ∏ b : Bool,
          generalSimplexIncidentProduct
            (H b) j (a b) y

/-- Arbitrary factors below the two copy-dependent AP majorants. -/
noncomputable def heterogeneousMaskSimplexMajorizedCutSystem
    (n N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Bool → Fin (n + 1) → Bool)
    (H : Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => ZMod N))
    (j : Fin (n + 1))
    (hrest :
      ∀ b t x,
        0 ≤ (H b).edgeWeight (j.succAbove t) x ∧
          (H b).edgeWeight (j.succAbove t) x ≤
            (apHeterogeneousSimplexSystem n N
              (apCopyMaskedFaceMajorant ν active b)).edgeWeight
                (j.succAbove t) x) :
    MajorizedCutSystem
      (Bool → ZMod N) (ZMod N) n where
  core := fun _ y => apFaceCenteredCore n N ν j y
  factor := fun a =>
    heterogeneousMaskSimplexTwoCopyCutTest n N H j a
  majorant := fun a =>
    apTwoCopyCutTest n N
      (apCopyMaskedFaceMajorant ν active) j a
  factor_nonneg := by
    intro a t z
    have hmono :=
      heterogeneousMaskSimplexTwoCopyCutTest_mono
        n N H
        (fun b =>
          apHeterogeneousSimplexSystem n N
            (apCopyMaskedFaceMajorant ν active b))
        j hrest a t z
    exact hmono.1
  factor_le_majorant := by
    intro a t z
    have hmono :=
      heterogeneousMaskSimplexTwoCopyCutTest_mono
        n N H
        (fun b =>
          apHeterogeneousSimplexSystem n N
            (apCopyMaskedFaceMajorant ν active b))
        j hrest a t z
    rw [←
      heterogeneousMaskSimplexTwoCopyCutTest_apHeterogeneous
        n N (apCopyMaskedFaceMajorant ν active)
        j a t z]
    exact hmono.2



namespace MajorizedCutSystem



end MajorizedCutSystem

/-! ## Arbitrary-factor quantitative bridge -/



/-- A Boolean pair of arbitrary simplex systems, with the first system in
the `false` copy and the second system in the `true` copy. -/
def heterogeneousMaskSimplexCopyPair
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)) :
    Bool →
      WeightedSimplexSystem
        (fun _ : Fin (n + 1) => G)
  | false => H
  | true => K





namespace HasLinearFormsCondition







end HasLinearFormsCondition

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.apCSHeterogeneousTerminalExponent.eq_1,
    `Wikipedia.SzemeredisTheorem.apCopyMaskedFaceMajorant.eq_1,
    `Wikipedia.SzemeredisTheorem.apTwoCopyHeterogeneousMaskedMajorizedCutSystem.congr_simp,
    `Wikipedia.SzemeredisTheorem.heterogeneousMaskSimplexCopyPair.match_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


