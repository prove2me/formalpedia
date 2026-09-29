-- Prove2me | Definitions.Def_Applications_AdjacentSumPolytopes_Necklace
-- name    : Applications_AdjacentSumPolytopes_Necklace
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:23:32.647853+00:00
-- url     : https://prove2.me/theorems/da257bf2-0316-427f-8f46-35d2b8e11e0d
-- title:
--   Aether Catalog definitions — Applications_AdjacentSumPolytopes_Necklace
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.AdjacentSumPolytopes.Necklace`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/AdjacentSumPolytopes/Necklace.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Basic
import Definitions.Def_Applications_AdjacentSumPolytopes_Growth
import Definitions.Def_Applications_AdjacentSumPolytopes_Recurrence

/-!
# Rotation action, Möbius recurrence, and a Gauss congruence

The cyclic adjacent-sum lattice points of length `n` carry an action of the cyclic group
of order `n` by rotation of coordinates.  When `n = p` is prime, the fixed-point formula
for `p`-groups yields a congruence between the cyclic count and the number of *constant*
points, i.e. the trace of the transfer matrix itself:

`#(cyclic points of length p) ≡ ⌊s/2⌋ + 1 = tr (adjMat s)  (mod p)`.

This is the first instance of the Gauss congruence `tr(Mⁿ) ≡ ∑_{d ∣ n} μ(n/d) tr(M^d) ≡ 0
(mod n)` for the transfer matrix, and it is exactly the statement that the *primitive*
(aperiodic) cyclic points of prime length come in orbits of size `p`.

We also set up the **Möbius recurrence** for the cyclic counts: the primitive counts
`primCyc s n = ∑_{(a,b) : ab = n} μ(a) · tr(M^b)` satisfy
`∑_{d ∣ n} primCyc s d = tr(Mⁿ)` for all `n > 0`, and `p ∣ primCyc s p` for `p` prime.

-- !-- Lab Notes -- !--
* **Hypothesis.** Rotation of a cyclic adjacent-sum point is again one; for prime length
  the only rotation-fixed points are the constant ones, which are exactly the "core"
  states `2a ≤ s`.  Hence the prime congruence.
* **Experiment.** `s = 2`, where `tr(adjMat 2) = ⌊2/2⌋ + 1 = 2`.  The cyclic counts for
  lengths `1..7` are `2, 6, 11, 26, 57, 129, 289`.  At the prime lengths:
  `tr(M²) = 6 ≡ 0 ≡ 2 (mod 2)`, `tr(M³) = 11 = 3·3 + 2 ≡ 2 (mod 3)`,
  `tr(M⁵) = 57 = 11·5 + 2 ≡ 2 (mod 5)`, `tr(M⁷) = 289 = 41·7 + 2 ≡ 2 (mod 7)` — all
  congruent to `tr(M) = 2`, as predicted.  Note the indexing: `cycCount s d` is the
  count for length `d + 1`.
* **Analysis.** The congruence survives; the primes are exactly where the fixed-point
  formula applies with no extra bookkeeping, and the general `n` case requires the full
  necklace/orbit decomposition, recorded as a conjecture.
* **Critique.** The proof is not vacuous: the fixed-point set is genuinely computed
  (`fixEquiv`), and it is nonempty (the origin is always a point), so the congruence has
  content on both sides.
-/

namespace AdjSum

open Finset Matrix

/-! ## The trace of the transfer matrix counts the core states -/


/-! ## The rotation action on cyclic points -/

/-- The type of cyclic adjacent-sum lattice points of length `q + 1`. -/
abbrev CycPt (s q : ℕ) := {x : Fin (q + 1) → Fin (s + 1) // x ∈ cycSet s q}

/-- Rotation of the coordinates of a cyclic point. -/
def rot (s q : ℕ) : Function.End (CycPt s q) := fun x =>
  ⟨fun i => x.1 (i + 1), by
    rw [mem_cycSet]
    intro i
    exact (mem_cycSet.mp x.2) (i + 1)⟩



/-- A rotation-fixed cyclic point is constant. -/
lemma fixed_const (s q : ℕ) (x : CycPt s q) (hx : rot s q x = x) (i : Fin (q + 1)) :
    x.1 i = x.1 0 := by
  have hstep : ∀ j : Fin (q + 1), x.1 (j + 1) = x.1 j := fun j =>
    congrFun (congrArg Subtype.val hx) j
  have key : ∀ k : ℕ, ∀ hk : k < q + 1, x.1 ⟨k, hk⟩ = x.1 0 := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
        intro hk
        have hk' : k < q + 1 := by omega
        have hq : 1 < q + 1 := by omega
        have hidx : (⟨k, hk'⟩ : Fin (q + 1)) + 1 = ⟨k + 1, hk⟩ := by
          refine Fin.ext ?_
          show (k + (1 : Fin (q + 1)).val) % (q + 1) = k + 1
          rw [Fin.val_one', Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hk]
        rw [← hidx, hstep ⟨k, hk'⟩]
        exact ih hk'
  exact key i.val i.isLt

/-- The rotation-fixed cyclic points are exactly the core states. -/
def fixEquiv (s q : ℕ) :
    Function.fixedPoints (rot s q) ≃ {a : Fin (s + 1) // 2 * (a : ℕ) ≤ s} where
  toFun := fun x => ⟨x.1.1 0, by
    have hc := fixed_const s q x.1 x.2
    have h := (mem_cycSet.mp x.1.2) 0
    rw [hc (0 + 1)] at h
    omega⟩
  invFun := fun a => ⟨⟨fun _ => a.1, by
      rw [mem_cycSet]
      intro i
      omega⟩, by
      show rot s q _ = _
      rfl⟩
  left_inv := by
    intro x
    refine Subtype.ext (Subtype.ext ?_)
    funext i
    exact (fixed_const s q x.1 x.2 i).symm
  right_inv := by
    intro a
    rfl

/-! ## The prime congruence -/



/-! ## The Möbius recurrence -/

/-- The trace sequence of the integral transfer matrix. -/
def traceSeq (s n : ℕ) : ℤ := Matrix.trace (adjMatZ s ^ n)

/-- The *primitive* cyclic counts, defined by Möbius inversion of the trace sequence. -/
def primCyc (s n : ℕ) : ℤ :=
  ∑ x ∈ n.divisorsAntidiagonal, ArithmeticFunction.moebius x.1 • traceSeq s x.2



end AdjSum


