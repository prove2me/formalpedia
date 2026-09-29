-- Prove2me | Definitions.Def_mme_stothers_phi134_cyclic_hash_data
-- name    : mme_stothers_phi134_cyclic_hash_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-05T09:36:08.244471+00:00
-- url     : https://prove2.me/theorems/1ca8e671-88eb-4baa-95c5-328c5a55a847
-- title:
--   Stothers $\Phi_{1,3,4}$ cyclic affine-hash data
-- statement:
--   For the exact $\Phi_{1,3,4}$ profile family in the fourth tensor power, this module defines the three-copy cyclic edge space, its three mode-word projections, coordinatewise-supported cyclic mixing, the affine type-2 hash in coefficient normal form, and the finite retained-edge family. The mode order is $(A_0,B_2,C_1)$, $(A_1,B_0,C_2)$, $(A_2,B_1,C_0)$, matching the cyclic construction used in the hashing argument.\n\nThese objects isolate the finite combinatorial interface needed to prove uniform hash retention and collision bounds before assembling the asymptotic value estimate.\n\n**Formalization Note** The hash is defined directly in coefficient normal form and reuses the already-published generic cyclic word code.
-- source:
--   A. M. Davie and A. J. Stothers, Improved bound for complexity of matrix multiplication, Proc. Roy. Soc. Edinburgh Sect. A 143 (2013), 351–369, Lemma 3.3 (pp. 359–361) and Lemma 5.1(iii) (p. 365), cyclic hashing specialization for the $\Phi_{1,3,4}$ fourth-power component.

import Definitions.Def_mme_stothers_phi134_profile_data
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash

open BigOperators

namespace MME.StothersFourth.Phi134

set_option autoImplicit false

/-- Three cyclic copies of the exact `phi_134` profile family.  Marginal
injectivity makes this also the full same-marginal family. -/
def CyclicExactEdge
    (N alpha beta gamma delta : ℕ) : Type :=
  ExactProfileAddress N alpha beta gamma delta ×
    (ExactProfileAddress N alpha beta gamma delta ×
      ExactProfileAddress N alpha beta gamma delta)

/-- A cyclic vertex records one mode word from each of the three copies. -/
abbrev CyclicModeWord (N : ℕ) : Type :=
  MME.StothersFourth.Phi233.CyclicModeWord N

/-- The three cyclic vertex projections, in the order
`(A₀,B₂,C₁)`, `(A₁,B₀,C₂)`, `(A₂,B₁,C₀)`. -/
def cyclicModeWord
    {N alpha beta gamma delta : ℕ}
    (e : CyclicExactEdge N alpha beta gamma delta) :
    Fin 3 → CyclicModeWord N
  | ⟨0, _⟩ =>
      (e.1.1.1 0, (e.2.1.1.1 2, e.2.2.1.1 1))
  | ⟨1, _⟩ =>
      (e.1.1.1 1, (e.2.1.1.1 0, e.2.2.1.1 2))
  | ⟨2, _⟩ =>
      (e.1.1.1 2, (e.2.1.1.1 1, e.2.2.1.1 0))
  | ⟨n + 3, h⟩ => absurd h (by omega)

/-- Form a three-mode address by taking mode zero from `x`, mode one from
`y`, and mode two from `z`. -/
def mixedAddress
    {N alpha beta gamma delta : ℕ}
    (x y z : MarginalAddress N alpha beta gamma delta) : ProfileAddress N
  | ⟨0, _⟩, j => x.1 0 j
  | ⟨1, _⟩, j => y.1 1 j
  | ⟨2, _⟩, j => z.1 2 j
  | ⟨n + 3, h⟩, _ => absurd h (by omega)

/-- Coordinatewise support of the three cyclic modewise mixtures. -/
def CyclicCoordinatewiseSupported
    {N alpha beta gamma delta : ℕ}
    (x y z : CyclicExactEdge N alpha beta gamma delta) : Prop :=
  CoordinatewiseSupported (mixedAddress x.1.1 y.1.1 z.1.1) ∧
    CoordinatewiseSupported
      (mixedAddress y.2.1.1 z.2.1.1 x.2.1.1) ∧
    CoordinatewiseSupported
      (mixedAddress z.2.2.1 x.2.2.1 y.2.2.1)

/-- A supported modewise mixture has the prescribed marginal histograms. -/
def mixedMarginalAddress
    {N alpha beta gamma delta : ℕ}
    (x y z : MarginalAddress N alpha beta gamma delta)
    (hsupport : CoordinatewiseSupported (mixedAddress x y z)) :
    MarginalAddress N alpha beta gamma delta := by
  refine ⟨mixedAddress x y z, hsupport, ?_⟩
  intro i k
  fin_cases i
  · simpa only [mixedAddress] using x.2.2 (0 : Fin 3) k
  · simpa only [mixedAddress] using y.2.2 (1 : Fin 3) k
  · simpa only [mixedAddress] using z.2.2 (2 : Fin 3) k

/-- Concrete finite enumeration of exact profile addresses. -/
noncomputable def exactProfileAddressFintype
    (N alpha beta gamma delta : ℕ) :
    Fintype (ExactProfileAddress N alpha beta gamma delta) :=
  @Subtype.fintype _ _ (Classical.decPred _)
    (@Subtype.fintype _ _ (Classical.decPred _) Pi.instFintype)

/-- Concrete finite enumeration of cyclic exact edges. -/
noncomputable def cyclicExactEdgeFintype
    (N alpha beta gamma delta : ℕ) :
    Fintype (CyclicExactEdge N alpha beta gamma delta) := by
  letI := exactProfileAddressFintype N alpha beta gamma delta
  unfold CyclicExactEdge
  infer_instance

/-- The full finite exact cyclic family. -/
noncomputable def edgeFinset
    (N alpha beta gamma delta : ℕ) :
    Finset (CyclicExactEdge N alpha beta gamma delta) := by
  letI := cyclicExactEdgeFintype N alpha beta gamma delta
  exact Finset.univ

/-- The reusable coefficient code of the cyclic type-2 hash. -/
abbrev cyclicHashModeCode
    (p N : ℕ) (i : Fin 3) (u : CyclicModeWord N) :
    Fin 3 → Fin (2 * N) → ZMod p :=
  MME.StothersFourth.Phi233.cyclicHashModeCode p N i u

/-- The cyclic affine hash in coefficient normal form.  Writing the hash in
this form makes vertex invariance and collision fibers immediate. -/
def cyclicAffineHash
    (p N alpha beta gamma delta : ℕ)
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p) (i : Fin 3)
    (e : CyclicExactEdge N alpha beta gamma delta) : ZMod p :=
  shift + (![0, 12 * offset, 6 * offset] : Fin 3 → ZMod p) i +
    ∑ r : Fin 3, ∑ j : Fin (2 * N),
      cyclicHashModeCode p N i (cyclicModeWord e i) r j * w r j

/-- Independent random coordinates for the cyclic affine hash. -/
def HashIndex (N : ℕ) : Type :=
  (Fin 3 × Fin (2 * N)) ⊕ Unit

/-- A weight word together with the progression-offset coordinate. -/
def HashState (p N : ℕ) : Type :=
  (HashIndex N → ZMod p) × ZMod p

/-- The three coordinate rows extracted from a hash state. -/
def stateWeights {p N : ℕ} (q : HashState p N) :
    Fin 3 → Fin (2 * N) → ZMod p :=
  fun r j ↦ q.1 (Sum.inl (r, j))

/-- The common label shift stored in the extra weight coordinate. -/
def stateShift {p N : ℕ} (q : HashState p N) : ZMod p :=
  q.1 (Sum.inr ())

/-- The cyclic hash evaluated from a complete state. -/
def stateHash
    (p N alpha beta gamma delta : ℕ)
    (q : HashState p N) (i : Fin 3)
    (e : CyclicExactEdge N alpha beta gamma delta) : ZMod p :=
  cyclicAffineHash p N alpha beta gamma delta
    (stateWeights q) (stateShift q) ((6 : ZMod p)⁻¹ * q.2) i e

/-- An edge is retained when all three vertices receive one allowed label. -/
def Retained
    (p N alpha beta gamma delta : ℕ) (S : Finset (ZMod p))
    (q : HashState p N)
    (e : CyclicExactEdge N alpha beta gamma delta) : Prop :=
  ∃ s ∈ S, ∀ i : Fin 3,
    stateHash p N alpha beta gamma delta q i e = s

/-- Exact cyclic edges retained by a fixed hash state. -/
noncomputable def retainedEdges
    (p N alpha beta gamma delta : ℕ) (S : Finset (ZMod p))
    (q : HashState p N) :
    Finset (CyclicExactEdge N alpha beta gamma delta) := by
  classical
  exact (edgeFinset N alpha beta gamma delta).filter
    (Retained p N alpha beta gamma delta S q)

/-- Canonical finite enumeration of the affine hash state space. -/
noncomputable instance hashStateFintype
    (p N : ℕ) [Fact p.Prime] : Fintype (HashState p N) := by
  unfold HashState HashIndex
  infer_instance

/-- Classical decidable equality on the finite hash state space. -/
noncomputable instance hashStateDecidableEq
    (p N : ℕ) : DecidableEq (HashState p N) :=
  Classical.decEq _

end MME.StothersFourth.Phi134


