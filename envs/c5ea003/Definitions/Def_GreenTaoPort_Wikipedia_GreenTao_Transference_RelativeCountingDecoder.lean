-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoder
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoder
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:08:16.981334+00:00
-- url     : https://prove2.me/theorems/55f9ca4e-780b-444a-b7db-69c1bba15346
-- title:
--   Decoding repeated weighted Cauchy–Schwarz parameters
-- statement:
--   For types $P,G$ in a common universe, the recursive stage parameter satisfies $\operatorname{CSStageParam}(P,G,0)=P$ and appends an endpoint pair after each elimination. Explicit equivalences decode it as $P\times(\mathrm{Fin}(r)\to G\times G)$, expose its base parameter and processed pairs, and transport finite-type instances.
--
--   The cube-axis equivalences separate distinguished coordinates, processed endpoint pairs, shared future coordinates, and unused uniform fibers. The iterator applies the majorized-cut transformation exactly $r$ times to a system of arity $n+r$, leaving arity $n$; a decoded version uses the explicit product parameter. Reindexing changes only the external parameterization. The active terminal exponent selects all vertices of active nondistinguished faces and reserves the distinguished face for the centered factor.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/RelativeCountingDecoder.lean#L26-L643

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingCertificate
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
# Stage decoders for relative-counting Cauchy--Schwarz recursion

Repeated applications of `MajorizedCutSystem.next` replace an external
parameter `P` by the left-associated tower

`(((P × (G × G)) × (G × G)) × ⋯)`.

The declarations below give this tower a stable stage-indexed name and
identify it with a base parameter together with a Boolean pair for every
coordinate already eliminated.  In the AP application the base parameter
is itself a Boolean pair, belonging to the distinguished omitted face.
Thus stage `r` is canonically a Boolean cube on `r + 1` axes.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## The nested parameter tower -/

/-- The external parameter type after `r` applications of
`MajorizedCutSystem.next`.

The recursion changes the base type before recurring.  Consequently
`CSStageParam P G (r + 1)` is definitionally
`CSStageParam (P × (G × G)) G r`, exactly the type produced by applying
`next` once and then iterating `r` more times. -/
def CSStageParam (P G : Type u) :
    ℕ → Type u
  | 0 => P
  | r + 1 => CSStageParam (P × (G × G)) G r

/-- Reassociate the decoded successor parameter so that the newest pair
becomes the head of a `Fin (r + 1)` tuple. -/
def csStageDecodedSuccEquiv
    (P G : Type u) (r : ℕ) :
    ((P × (G × G)) × (Fin r → G × G)) ≃
      P × (Fin (r + 1) → G × G) where
  toFun q :=
    (q.1.1, Fin.cons q.1.2 q.2)
  invFun q :=
    ((q.1, q.2 0), Fin.tail q.2)
  left_inv q := by
    rcases q with ⟨⟨p, a⟩, rest⟩
    apply Prod.ext
    · exact Prod.ext rfl rfl
    · funext i
      rfl
  right_inv q := by
    rcases q with ⟨p, pairs⟩
    apply Prod.ext
    · rfl
    · exact Fin.cons_self_tail pairs

/-- Decode the nested `next` parameter into the original parameter and
one ordered pair for every eliminated coordinate. -/
def csStageParamEquiv
    (P G : Type u) :
    ∀ r : ℕ,
      CSStageParam P G r ≃
        P × (Fin r → G × G)
  | 0 =>
      { toFun := fun p => (p, fun i => Fin.elim0 i)
        invFun := fun q => q.1
        left_inv := fun _ => rfl
        right_inv := by
          intro q
          rcases q with ⟨p, empty⟩
          apply Prod.ext
          · rfl
          · funext i
            exact Fin.elim0 i }
  | r + 1 =>
      (csStageParamEquiv (P × (G × G)) G r).trans
        (csStageDecodedSuccEquiv P G r)

/-- Finiteness of a stage parameter is transported from its decoded
product representation. -/
noncomputable instance csStageParamFintype
    {P G : Type u} [Fintype P] [Fintype G] {r : ℕ} :
    Fintype (CSStageParam P G r) :=
  Fintype.ofEquiv
    (P × (Fin r → G × G))
    (csStageParamEquiv P G r).symm

/-- The original external parameter retained inside a stage parameter. -/
def CSStageParam.base
    {P G : Type u} {r : ℕ}
    (p : CSStageParam P G r) : P :=
  (csStageParamEquiv P G r p).1

/-- The ordered endpoint pair belonging to an already eliminated
coordinate. -/
def CSStageParam.pair
    {P G : Type u} {r : ℕ}
    (p : CSStageParam P G r) (i : Fin r) : G × G :=
  (csStageParamEquiv P G r p).2 i









/-! ## Boolean-axis form of the AP parameter -/







/-! ## Full AP cube decoder -/

/-- Split a doubled tuple into the distinguished coordinate and the
canonically ordered tuple of all other doubled coordinates. -/
def apProjectionAxesEquiv
    (G : Type u) (n : ℕ) (j : Fin (n + 1)) :
    (Fin (n + 1) → Bool → G) ≃
      (Bool → G) × (Fin n → Bool → G) where
  toFun x :=
    (x j, fun t => x (j.succAbove t))
  invFun q :=
    Fin.insertNth j q.1 q.2
  left_inv x := by
    apply (Fin.insertNth_eq_iff).2
    exact ⟨rfl, rfl⟩
  right_inv q := by
    rcases q with ⟨a, y⟩
    apply Prod.ext
    · funext b
      simp
    · funext t b
      simp

/-- Split the doubled deleted-coordinate tuple at Cauchy--Schwarz stage
`r`.

The output consists of:

* endpoint pairs for the `r` processed coordinates;
* the shared `false` values for the `s` future coordinates;
* the unused pair at the current coordinate;
* the unused `true` values for the future coordinates.

The deleted-coordinate count is `r + (s + 1)`: processed coordinates,
the current coordinate, and future coordinates. -/
def csStageDeletedAxesEquiv
    (G : Type u) (r s : ℕ) :
    (Fin (r + (s + 1)) → Bool → G) ≃
      (((Fin r → G × G) × (Fin s → G)) ×
        ((G × G) × (Fin s → G))) where
  toFun x :=
    (((fun i =>
        boolEndpointEquiv G
          (x (Fin.castAdd (s + 1) i))),
      fun t =>
        x (Fin.natAdd r t.succ) false),
    (boolEndpointEquiv G
        (x (Fin.natAdd r (0 : Fin (s + 1)))),
      fun t =>
        x (Fin.natAdd r t.succ) true))
  invFun q :=
    Fin.append
      (fun i => selectPair (q.1.1 i))
      (Fin.cons
        (selectPair q.2.1)
        (fun t b =>
          if b then q.2.2 t else q.1.2 t))
  left_inv x := by
    funext i b
    refine Fin.addCases (m := r) (n := s + 1) ?_ ?_ i
    · intro t
      dsimp only
      rw [Fin.append_left]
      exact congrFun
        (selectPair_boolEndpointEquiv
          (x (Fin.castAdd (s + 1) t))) b
    · intro t
      dsimp only
      rw [Fin.append_right]
      refine Fin.cases ?_ (fun q => ?_) t
      · exact congrFun
          (selectPair_boolEndpointEquiv
            (x (Fin.natAdd r (0 : Fin (s + 1))))) b
      · cases b <;> rfl
  right_inv q := by
    rcases q with
      ⟨⟨processed, futureFalse⟩,
        ⟨current, futureTrue⟩⟩
    apply Prod.ext
    · apply Prod.ext
      · funext i
        dsimp only
        rw [Fin.append_left]
        exact
          (boolEndpointEquiv G).right_inv
            (processed i)
      · funext t
        dsimp only
        rw [Fin.append_right]
        rfl
    · apply Prod.ext
      · dsimp only
        rw [Fin.append_right]
        exact
          (boolEndpointEquiv G).right_inv current
      · funext t
        dsimp only
        rw [Fin.append_right]
        rfl

/-- Decode a full AP Boolean cube at stage `r`, with `s + 1` live
deleted coordinates.

The first output component is precisely the parameter and live tail
averaged by `headMajorantMean`.  The second component consists entirely of
uniform fibers ignored by that moment: the current coordinate pair and the
future `true` tuple. -/
def apCSStageCubeEquiv
    (r s N : ℕ)
    (j : Fin ((r + (s + 1)) + 1)) :
    CubePoint ((r + (s + 1)) + 1) N ≃
      ((CSStageParam (Bool → ZMod N) (ZMod N) r ×
          (Fin s → ZMod N)) ×
        ((ZMod N × ZMod N) × (Fin s → ZMod N))) := by
  let split :=
    (apProjectionAxesEquiv
      (ZMod N) (r + (s + 1)) j).trans
      (Equiv.prodCongr
        (Equiv.refl (Bool → ZMod N))
        (csStageDeletedAxesEquiv (ZMod N) r s))
  exact
    split.trans
      { toFun := fun q =>
          (((csStageParamEquiv
                (Bool → ZMod N) (ZMod N) r).symm
              (q.1, q.2.1.1),
            q.2.1.2),
          q.2.2)
        invFun := fun q =>
          let decoded :=
            csStageParamEquiv
              (Bool → ZMod N) (ZMod N) r q.1.1
          (decoded.1,
            ((decoded.2, q.1.2), q.2))
        left_inv := by
          intro q
          rcases q with
            ⟨a, ⟨⟨processed, futureFalse⟩, unused⟩⟩
          simp
        right_inv := by
          intro q
          rcases q with
            ⟨⟨p, futureFalse⟩, unused⟩
          simp }











/-! ## Expected CFZ selectors at a decoded stage -/







/-- At the terminal stage, every vertex on every active non-distinguished
face has been generated; the distinguished face remains reserved for the
centered factor. -/
def apCSActiveTerminalExponent
    {k : ℕ}
    (active : Fin k → Bool) (j : Fin k) :
    LinearFormsExponent k :=
  fun i _ω =>
    if i = j then false else active i





/-! ## Iterating `MajorizedCutSystem.next` -/

namespace MajorizedCutSystem

/-- Change only the external parameterization of a cut system. -/
def reindex
    {P Q G : Type u} {n : ℕ}
    (S : MajorizedCutSystem P G n)
    (e : Q ≃ P) :
    MajorizedCutSystem Q G n where
  core := fun q => S.core (e q)
  factor := fun q => S.factor (e q)
  majorant := fun q => S.majorant (e q)
  factor_nonneg := fun q => S.factor_nonneg (e q)
  factor_le_majorant := fun q => S.factor_le_majorant (e q)















/-- Apply `next` exactly `r` times to a system with `n + r` live
coordinates.  The result has the definitionally correct nested parameter
`CSStageParam P G r` and `n` remaining coordinates. -/
def iterNext
    {P G : Type u} {n : ℕ} :
    ∀ r : ℕ,
      MajorizedCutSystem P G (n + r) →
        MajorizedCutSystem (CSStageParam P G r) G n
  | 0, S => S
  | r + 1, S => iterNext r S.next





/-- At a completed stage, the parameter type is the initial parameter
together with one endpoint pair for every original coordinate. -/
def iterNextDecoded
    {P G : Type u} {n r : ℕ}
    (S : MajorizedCutSystem P G (n + r)) :
    MajorizedCutSystem
      (P × (Fin r → G × G)) G n :=
  (iterNext r S).reindex
    (csStageParamEquiv P G r).symm











end MajorizedCutSystem

/-! ## Quantitative endpoint after the decoded first stage -/



end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.CSStageParam.base.eq_1,
    `Wikipedia.SzemeredisTheorem.CSStageParam.match_1,
    `Wikipedia.SzemeredisTheorem.CSStageParam.pair.eq_1,
    `Wikipedia.SzemeredisTheorem.MajorizedCutSystem.iterNext.match_1,
    `Wikipedia.SzemeredisTheorem.apCSActiveTerminalExponent.eq_1,
    `Wikipedia.SzemeredisTheorem.apCSStageCubeEquiv.eq_1,
    `Wikipedia.SzemeredisTheorem.apProjectionAxesEquiv.eq_1,
    `Wikipedia.SzemeredisTheorem.csStageDeletedAxesEquiv.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


