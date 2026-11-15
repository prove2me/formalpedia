-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingCertificate
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingCertificate
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:07:09.203101+00:00
-- url     : https://prove2.me/theorems/9c2e575f-fe42-4f09-9232-c1b84dbad4c9
-- title:
--   Centered AP-face cores and masked two-copy cut systems
-- statement:
--   The centered core on a selected AP face is $\nu$ evaluated on its canonical simplex form, minus one. The two-copy cut test reconstructs each incident face factor from two independent values of the missing coordinate, multiplying the two corresponding heterogeneous face weights.
--
--   The bundle identifies Boolean-indexed endpoints with an ordinary pair. Given pointwise bounds on all untouched colours, it packages the centered core and two-copy tests as a majorized cut system: active colours are bounded by their AP majorants and inactive colours by one. This is the concrete input to the weighted Cauchy–Schwarz certificate construction.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/RelativeCountingCertificate.lean#L161-L539

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedFaceCutClosure
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearFormsCS
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
# CFZ certificates for projected two-copy correlations

The active-majorant induction in relative counting produces a two-copy
correlation.  The coordinate on the selected face is shared, while the
omitted simplex coordinate has two independent copies.  This file realizes
that correlation as a `MajorizedCutSystem`.

The first part supplies a reusable terminal-value theorem for systems whose
designated majorants are all one.  It identifies the fully iterated
Cauchy--Schwarz endpoint with the box moment of the original core.  Applied
to the centered AP face, the box moment is exactly `faceCenteredProduct`.

The second part defines the concrete two-copy AP cut factors and proves that
their system form is the projected correlation occurring in densification.
For factors bounded by one this gives an explicit, kernel-checked
`HasCFZCertificate`, and hence plugs the exact projected expression into the
weighted Cauchy--Schwarz API.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

namespace MajorizedCutSystem

/-! ## Terminal values for unit-majorant systems -/











end MajorizedCutSystem

/-! ## The centered AP face as a box core -/

/-- The selected AP face, centered at one, in canonical `Fin n`
deleted-face coordinates. -/
noncomputable def apFaceCenteredCore
    (n N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin (n + 1))
    (y : Fin n → ZMod N) : ℝ :=
  ν (apSimplexForm (n + 1) N j
      (finTupleToDeletedVector j y)) - 1



namespace MajorizedCutSystem





end MajorizedCutSystem

/-! ## Concrete two-copy AP cut factors -/

/-- Reconstruct the `t`-th deleted-coordinate factor in the projected
two-copy correlation.

The parameter `a : Bool → ZMod N` contains the two independent copies of
the omitted coordinate `j`.  The input `z` contains every shared coordinate
except `t`; an irrelevant zero is inserted at `t`, since the corresponding
simplex face omits that coordinate. -/
def apTwoCopyCutTest
    (n N : ℕ)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (a : Bool → ZMod N) :
    CutTestFamily (ZMod N) n := by
  cases n with
  | zero =>
      exact fun t => Fin.elim0 t
  | succ m =>
      exact fun t z =>
        ∏ b : Bool,
          g b (j.succAbove t)
            (apSimplexForm (m + 2) N (j.succAbove t)
              (deleteCoordinate
                (Fin.insertNth j (a b)
                  (Fin.insertNth t 0 z))
                (j.succAbove t)))









/-- Componentwise nonnegative domination of two face families gives
pointwise domination of their reconstructed two-copy cut tests. -/
theorem apTwoCopyCutTest_mono
    (n N : ℕ)
    (g h : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hgh :
      ∀ b t z,
        0 ≤ g b (j.succAbove t) z ∧
          g b (j.succAbove t) z ≤
            h b (j.succAbove t) z)
    (a : Bool → ZMod N)
    (t : Fin n) (z : Fin (n - 1) → ZMod N) :
    0 ≤ apTwoCopyCutTest n N g j a t z ∧
      apTwoCopyCutTest n N g j a t z ≤
        apTwoCopyCutTest n N h j a t z := by
  cases n with
  | zero =>
      exact Fin.elim0 t
  | succ m =>
      constructor
      · unfold apTwoCopyCutTest
        exact Finset.prod_nonneg fun b _ => (hgh b t _).1
      · unfold apTwoCopyCutTest
        exact Finset.prod_le_prod
          (fun b _ => (hgh b t _).1)
          (fun b _ => (hgh b t _).2)

/-! ## A single paid active face -/











/-- Boolean-indexed endpoints and an ordinary pair carry the same two
values. -/
def boolEndpointEquiv (G : Type*) :
    (Bool → G) ≃ G × G where
  toFun a := (a false, a true)
  invFun p := selectPair p
  left_inv a := by
    funext b
    cases b <;> rfl
  right_inv p :=
    Prod.ext rfl rfl

@[simp]
theorem selectPair_boolEndpointEquiv
    {G : Type*} (a : Bool → G) :
    selectPair (boolEndpointEquiv G a) = a :=
  (boolEndpointEquiv G).left_inv a



/-! ## Mixed active-majorant system -/

/-- The exact majorized system used before the active-majorant induction
has removed all sparse faces.

For an active colour, both two-copy factors are dominated by the
corresponding AP majorant `ν`; for an inactive colour they are dominated by
one. -/
noncomputable def apTwoCopyMaskedMajorizedCutSystem
    (n N : ℕ)
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (g : Bool → APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apMaskedFaceMajorant ν active) j) :
    MajorizedCutSystem
      (Bool → ZMod N) (ZMod N) n where
  core := fun _ y => apFaceCenteredCore n N ν j y
  factor := fun a => apTwoCopyCutTest n N g j a
  majorant := fun a =>
    apTwoCopyCutTest n N
      (fun _ => apMaskedFaceMajorant ν active) j a
  factor_nonneg := fun a t z =>
    (apTwoCopyCutTest_mono n N g
      (fun _ => apMaskedFaceMajorant ν active)
      j (fun b t z => hrest b t z) a t z).1
  factor_le_majorant := fun a t z =>
    (apTwoCopyCutTest_mono n N g
      (fun _ => apMaskedFaceMajorant ν active)
      j (fun b t z => hrest b t z) a t z).2











/-! ## The bounded two-copy certificate -/













end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.apTwoCopyCutTest.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


