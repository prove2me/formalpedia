-- Prove2me | Definitions.Def_Probability_FourierExtremalEvidence
-- name    : Probability_FourierExtremalEvidence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:16:20.815254+00:00
-- url     : https://prove2.me/theorems/11f8f087-8172-4e0c-bfc4-8f5a3962dccb
-- title:
--   Aether Catalog definitions — Probability_FourierExtremalEvidence
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.FourierExtremalEvidence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/FourierExtremalEvidence.lean by skeleton subtraction
import Mathlib
/-
# Lab notes: exhaustive computational evidence on `ℤ/4`

This file is the experimental companion to `Catalog.Probability.FourierExtremalConverse`,
`Catalog.Probability.FourierExtremalAlgebra` and `Catalog.Probability.FourierExtremalConvolution`.
On `G = ℤ/4` all characters take values in the Gaussian integers `ℤ[i]`, so the discrete Fourier
transform can be computed *exactly* with integer arithmetic and the whole classification can be
checked by brute force.

We enumerate all `5^4 = 625` functions `ℤ/4 → {0, 1, -1, i, -i}` and record:

| experiment                                                        | result |
|-------------------------------------------------------------------|--------|
| functions tested / nonzero                                        | 625 / 624 |
| uncertainty principle `|supp f| * |supp f̂| ≥ 4` holds             | `true` |
| number of extremals in the sample                                 | 48 |
| support-size distribution of the extremals (sizes 0,1,2,3,4)      | 0, 16, 16, 0, 16 |
| every extremal support is a coset (`x - y + z` closure)           | `true` |
| every extremal has constant modulus on its support                | `true` |
| the frequency support of every extremal is a coset                | `true` |
| pointwise products of extremals are zero or extremal              | `true` |
| convolutions of extremals are zero or extremal                    | `true` |
| the non-coset support `{0,1}` is *not* extremal (`2 * 3 = 6 > 4`) | confirmed |

The absence of extremals of support size `3` is exactly the prediction of the classification:
`3` is not the order of a subgroup of `ℤ/4`. The counted numbers `16 = 4 · 4` for size `1`
(`4` positions times `4` unit values), `16 = 2 · 4 · 2` for size `2` (`2` cosets of `{0,2}`,
`4` values, `2` characters modulo the annihilator) and `16 = 4 · 4` for size `4`
(`4` characters times `4` values) also match the classification exactly.

The final `theorem z4_extremals_are_cosets` turns the central check into a kernel-verified
statement (via `decide`, not `native_decide`).
-/


namespace FourierEvidenceZ4

/-- Gaussian integers as pairs, enough to hold all 4th roots of unity. -/
abbrev GI := Int × Int

def gadd (z w : GI) : GI := (z.1 + w.1, z.2 + w.2)
def gmul (z w : GI) : GI := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)
def conjg (z : GI) : GI := (z.1, -z.2)

def ipow (m : Nat) : GI :=
  match m % 4 with
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | _ => (0, -1)

def val (f : List GI) (x : Nat) : GI := f.getD x (0, 0)

def dftAt (f : List GI) (k : Nat) : GI :=
  (List.range 4).foldl (fun acc x => gadd acc (gmul (conjg (ipow (k * x))) (val f x))) (0, 0)

def suppSet (f : List GI) : List Nat := (List.range 4).filter (fun x => val f x != (0, 0))
def dftSuppSet (f : List GI) : List Nat := (List.range 4).filter (fun k => dftAt f k != (0, 0))

def isZeroFun (f : List GI) : Bool := suppSet f == []
def isExtremal (f : List GI) : Bool := (suppSet f).length * (dftSuppSet f).length == 4

/-- Is the support closed under `x - y + z` (i.e. a coset of a subgroup)? -/
def isCoset (S : List Nat) : Bool :=
  S.all fun x => S.all fun y => S.all fun z => S.contains ((x + 4 - y + z) % 4)


def vals : List GI := [(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)]

def allFuns : List (List GI) :=
  vals.flatMap fun a => vals.flatMap fun b => vals.flatMap fun c => vals.map fun d => [a, b, c, d]

def nonzeroFuns : List (List GI) := allFuns.filter (fun f => !isZeroFun f)

def extremals : List (List GI) := nonzeroFuns.filter isExtremal

-- uncertainty principle holds for every nonzero test function
-- number of extremals in the sample
-- every extremal support is a coset
-- every extremal is flat
-- the frequency support of every extremal is also a coset (of the dual group)
-- distribution of support sizes among extremals
-- non-extremal example: supports {0,1}
-- pointwise products of extremals are zero or extremal
-- convolutions of extremals are zero or extremal

end FourierEvidenceZ4


