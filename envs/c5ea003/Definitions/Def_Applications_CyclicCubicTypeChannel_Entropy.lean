-- Prove2me | Definitions.Def_Applications_CyclicCubicTypeChannel_Entropy
-- name    : Applications_CyclicCubicTypeChannel_Entropy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:42:00.64159+00:00
-- url     : https://prove2.me/theorems/6bbd35ce-ba21-4c7b-9b04-1af9d3de63a5
-- title:
--   Aether Catalog definitions — Applications_CyclicCubicTypeChannel_Entropy
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.CyclicCubicTypeChannel.Entropy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/CyclicCubicTypeChannel/Entropy.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
import Definitions.Def_Applications_LabelEntropyDeficit
/-
# The cyclic-cubic type channel: full pinning, and its failure for semiprimes

## Context (FACT round-32 #3, "THE-CYCLIC-CUBIC-IS-FULLY-PINNED", paper 122)

`Applications.CyclicCubicTypeChannel.Splitting` proves the arithmetic law: an
unramified prime `p` has residue degree `1` in `K = ℚ(ζ₇ + ζ₇⁻¹)` iff
`p ≡ ±1 (mod 7)`, and residue degree `3` otherwise — **two types only**.

This file turns that law into an information channel and computes its capacity
exactly, in bits, using the Shannon-entropy functional of
`Applications.LabelEntropyDeficit`.  Modelling `p mod 7` as uniform on the six
invertible residues (Chebotarev/Dirichlet equidistribution), we prove:

* `CyclicCubic.H_typeMarginal` — the type entropy is exactly
  `H(T) = log₂ 3 − 2/3 = 0.918296…` bits (experiment: `0.9179`);
* `CyclicCubic.mutualInfo_residue_type` — `I(p mod 7 ; T) = log₂ 3 − 2/3`, i.e.
  `I = H(T)` **exactly**: the type is fully pinned by the residue
  (`CyclicCubic.full_pinning`), and the channel leaks nothing more
  (`CyclicCubic.pinning_saturates`, `I ≤ H(T)` with equality);
* `CyclicCubic.mutualInfo_semiprime` — for a *semiprime* `N = p·q` the residue
  `N mod 7` retains only `log₂ 3 − 10/9 = 0.473852…` bits about the unordered
  type pair (experiment: `0.4747`): pinning is destroyed by multiplication;
* `CyclicCubic.which_factor_information_zero` — the *ordered* type pair carries
  exactly the same information as the unordered one, so the residue reveals
  **0.0000** bits about *which* factor has which type; the underlying exact
  symmetry is `CyclicCubic.countOrd_swap`.

All entropies are computed in closed form; numerical bounds
(`CyclicCubic.H_typeMarginal_bounds`, `CyclicCubic.mutualInfo_semiprime_bounds`)
are derived from kernel-checked integer inequalities `2^1584 < 3^1000 < 2^1585`.
-/

open Finset LabelEntropy

namespace CyclicCubic

/-! ## Entropy of a finitely-valued distribution given in case form -/

section EntropyTools

variable {ι : Type*} [Fintype ι]




end EntropyTools

/-! ## Mutual information of a joint distribution -/

/-- Mutual information, in bits, of a joint distribution on a product of finite
types: `I(X;Y) = H(X) + H(Y) − H(X,Y)`. -/
noncomputable def MI {α β : Type*} [Fintype α] [Fintype β] (w : α × β → ℝ) : ℝ :=
  H Finset.univ (fun a : α => ∑ b : β, w (a, b))
    + H Finset.univ (fun b : β => ∑ a : α, w (a, b))
    - H Finset.univ w

/-! ## Logarithm values -/












/-! ## Numerical bounds on `log₂ 3` -/



/-! ## The type map -/

/-- The **splitting type** of a residue class: `true` = split completely
(residue degree `1`), `false` = inert (residue degree `3`). -/
def resType (a : ZMod 7) : Bool := decide (a = 1 ∨ a = 6)



/-! ## The single-prime channel `p mod 7 ⟶ type` -/

/-- The six invertible residues mod `7`. -/
def units7 : Finset (ZMod 7) := Finset.univ.erase 0

/-- Number of invertible residues with residue `n` and type `b` (so `0` or `1`). -/
def countRT (n : ZMod 7) (b : Bool) : ℕ :=
  (units7.filter (fun u => u = n ∧ resType u = b)).card




/-- Joint law of `(p mod 7, type of p)` under the uniform law on invertible
residues. -/
noncomputable def pRT (q : ZMod 7 × Bool) : ℝ := (countRT q.1 q.2 : ℝ) / 6











/-! ## The semiprime channel `N = p·q mod 7 ⟶ unordered type pair` -/

/-- The `36` ordered pairs of invertible residues. -/
def pairs7 : Finset (ZMod 7 × ZMod 7) := Finset.univ.filter (fun q => q.1 ≠ 0 ∧ q.2 ≠ 0)

/-- How many of the two factors split (an unordered type pair). -/
def splitCount (u v : ZMod 7) : Fin 3 :=
  if resType u ∧ resType v then 2 else if resType u ∨ resType v then 1 else 0

/-- Count of factorisations of `n` with a given unordered type pair. -/
def countSemi (n : ZMod 7) (k : Fin 3) : ℕ :=
  (pairs7.filter (fun q => q.1 * q.2 = n ∧ splitCount q.1 q.2 = k)).card

/-- `n` is a nonzero class of "split" type (`n ≡ ±1`). -/
def clsA (n : ZMod 7) : Prop := n = 1 ∨ n = 6

/-- `n` is a nonzero class of "inert" type. -/
def clsB (n : ZMod 7) : Prop := n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 6

instance (n : ZMod 7) : Decidable (clsA n) := by unfold clsA; infer_instance
instance (n : ZMod 7) : Decidable (clsB n) := by unfold clsB; infer_instance




/-- Joint law of `(N mod 7, unordered type pair)` for `N = p·q` with `p, q`
independent and uniform on invertible residues. -/
noncomputable def pSemi (q : ZMod 7 × Fin 3) : ℝ := (countSemi q.1 q.2 : ℝ) / 36











/-! ## Which factor is which: exactly zero bits -/

/-- Count of factorisations of `n` with a given *ordered* pair of types. -/
def countOrd (n : ZMod 7) (b : Bool × Bool) : ℕ :=
  (pairs7.filter (fun q => q.1 * q.2 = n ∧ (resType q.1, resType q.2) = b)).card





/-- Joint law of `(N mod 7, ordered pair of types)`. -/
noncomputable def pOrd (q : ZMod 7 × (Bool × Bool)) : ℝ := (countOrd q.1 q.2 : ℝ) / 36











end CyclicCubic


