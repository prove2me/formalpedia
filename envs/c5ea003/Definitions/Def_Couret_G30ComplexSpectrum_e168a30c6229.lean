-- Prove2me | Definitions.Def_Couret_G30ComplexSpectrum_e168a30c6229
-- name    : Couret_G30ComplexSpectrum_e168a30c6229
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T17:22:29.568267+00:00
-- url     : https://prove2.me/theorems/7aebd3b7-3c4f-49dd-ae03-29332470b193
-- title:
--   Exact finite Gaussian spectra and directed permutation certificates on eight unit labels
-- statement:
--   Let $V=\{0,\ldots,7\}$, whose ordered unit labels are $(1,7,11,13,17,19,23,29)$. Their fixed $C_2\times C_4$ coordinates are $((0,0),(0,1),(1,2),(0,3),(1,3),(0,2),(1,1),(1,0))$. The list $\mathcal T$ enumerates increasing triples of distinct indices from $V$. For $(m,n)\in\{0,1\}\times\{0,1,2,3\}$ and coordinate $(a,b)$, use $\chi_{m,n}=(-1)^{ma}i^{nb}$ and $\lambda_{m,n}(T)=\sum_{x\in T}\chi_{m,n}(x)$, represented exactly as an integer pair in $\mathbb Z[i]$. The definitions implement Gaussian integer addition, multiplication and squared norm as integer-pair arithmetic. The eight character sums yield a 49-bin complex spectral histogram on $[-3,3]^2$ and a ten-bin squared-norm profile on $0,\ldots,9$. Fixed representative lists, class-size filters and the distinguished support $T_C=[0,2,7]$ organize the 56 increasing triples. A coordinate-based operation modulo $(2,4)$ defines directed Cayley edge Booleans. The permutation checker tests list length eight, distinct entries, and equality of every source edge with the corresponding target edge. Five explicit permutation lists supply concrete isomorphism certificates. These objects establish a finite computational framework; no global analytic statement is part of these definitions.
-- source:
--   https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/g30-gate-b-lean/G30ComplexSpectrum.lean; Proofs mechanically replaced by kernel decide using Lean-oracle declaration ranges; statement spans preserved. Validated in https://github.com/alexcour/couret-finite-verifications/actions/runs/42503615738

import Mathlib.Tactic
import Mathlib.Tactic
set_option maxHeartbeats 0

set_option autoImplicit false
set_option maxRecDepth 1000000

/-!
Gate B candidate formalization for the 56 three-subsets of U(30).

Scope:
* exact finite complex Fourier spectra over Gaussian integers;
* ten spectral classes, certified by ten explicit representatives;
* power-profile classes 32/24;
* exact complex spectral fiber of T_C = {1,11,29}, of size 5;
* explicit graph-isomorphism certificates for the five members of that fiber.

Status on 2026-10-07:
P-SCAFFOLD. This file was generated after an independent exact Python replay, but
was NOT compiled in the present execution environment because no Lean binary is
installed there. Promotion to D-Lean requires a pinned Lean/Mathlib build and an
archived build log + SHA-256 manifest.

No RH, Hilbert-Polya, prime-distribution, or asymptotic claim is made here.
-/

namespace CouretUnification.G30ComplexSpectrum

abbrev V := Fin 8
abbrev GZ := Prod Int Int
abbrev CharIdx := Prod (Fin 2) (Fin 4)

@[inline] def gAdd (z w : GZ) : GZ := (z.1 + w.1, z.2 + w.2)
@[inline] def gMul (z w : GZ) : GZ :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)
@[inline] def gNormSq (z : GZ) : Int := z.1 * z.1 + z.2 * z.2

@[inline] def iPow (n : Nat) : GZ :=
  match n % 4 with
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | _ => (0, -1)

@[inline] def signPow (n : Nat) : GZ :=
  if n % 2 = 0 then (1, 0) else (-1, 0)

@[inline] def unitValue (i : V) : Nat :=
  match i.val with
  | 0 => 1 | 1 => 7 | 2 => 11 | 3 => 13
  | 4 => 17 | 5 => 19 | 6 => 23 | _ => 29

@[inline] def crtCoord (i : V) : Prod Nat Nat :=
  match i.val with
  | 0 => (0, 0) | 1 => (0, 1) | 2 => (1, 2) | 3 => (0, 3)
  | 4 => (1, 3) | 5 => (0, 2) | 6 => (1, 1) | _ => (1, 0)

@[inline] def evalChar (c : CharIdx) (i : V) : GZ :=
  let (m, n) := c
  let (a, b) := crtCoord i
  gMul (signPow (m.val * a)) (iPow (n.val * b))

def allChars : List CharIdx :=
  [(0,0), (0,1), (0,2), (0,3), (1,0), (1,1), (1,2), (1,3)]

def vertices : List V := [0,1,2,3,4,5,6,7]

def choose2 : List V -> List (List V)
  | [] => []
  | a :: rest => (rest.map (fun b => [a,b])) ++ choose2 rest

def choose3 : List V -> List (List V)
  | [] => []
  | a :: rest => ((choose2 rest).map (fun p => a :: p)) ++ choose3 rest

def triplets : List (List V) := choose3 vertices



@[inline] def charSum (T : List V) (c : CharIdx) : GZ :=
  T.foldl (fun acc i => gAdd acc (evalChar c i)) (0,0)

-- Every Fourier sum of a 3-set lies in [-3,3]^2.
def gaussianGrid : List GZ :=
  [(-3,-3),(-3,-2),(-3,-1),(-3,0),(-3,1),(-3,2),(-3,3),
   (-2,-3),(-2,-2),(-2,-1),(-2,0),(-2,1),(-2,2),(-2,3),
   (-1,-3),(-1,-2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),
   (0,-3),(0,-2),(0,-1),(0,0),(0,1),(0,2),(0,3),
   (1,-3),(1,-2),(1,-1),(1,0),(1,1),(1,2),(1,3),
   (2,-3),(2,-2),(2,-1),(2,0),(2,1),(2,2),(2,3),
   (3,-3),(3,-2),(3,-1),(3,0),(3,1),(3,2),(3,3)]

def spectrumCovered : Bool :=
  triplets.all (fun T => allChars.all (fun c => gaussianGrid.contains (charSum T c)))



def complexSpectrumCounts (T : List V) : List Nat :=
  let vals := allChars.map (charSum T)
  gaussianGrid.map (fun z => vals.count z)

def sameComplexSpectrum (T U : List V) : Bool :=
  complexSpectrumCounts T == complexSpectrumCounts U

def powerCounts (T : List V) : List Nat :=
  let vals := allChars.map (fun c => gNormSq (charSum T c))
  (List.range 10).map (fun n => vals.count (Int.ofNat n))

def samePower (T U : List V) : Bool := powerCounts T == powerCounts U

-- One representative per exact complex spectral class, in lexicographic order.
def spectralReps : List (List V) :=
  [[0,1,2], [0,1,3], [0,1,4], [0,1,5], [1,2,3],
   [1,2,4], [1,2,5], [1,2,6], [1,2,7], [1,3,5]]

def spectralClassSize (R : List V) : Nat :=
  (triplets.filter (fun T => sameComplexSpectrum T R)).length

def repsPairwiseDistinct : List (List V) -> Bool
  | [] => true
  | r :: rs => rs.all (fun s => !(sameComplexSpectrum r s)) && repsPairwiseDistinct rs

def repsComplete : Bool :=
  triplets.all (fun T => spectralReps.any (fun R => sameComplexSpectrum T R))









-- The two old power/energy classes: 32 and 24.
def powerReps : List (List V) := [[0,1,2], [0,1,3]]
def powerClassSize (R : List V) : Nat :=
  (triplets.filter (fun T => samePower T R)).length



def TC : List V := [0,2,7]
def tcFiber : List (List V) :=
  triplets.filter (fun T => sameComplexSpectrum T TC)





-- Group law in C2 x C4, represented with the same coordinates as the legacy file.
@[inline] def indexFromCoord (a b : Nat) : V :=
  match a % 2, b % 4 with
  | 0,0 => 0 | 0,1 => 1 | 1,2 => 2 | 0,3 => 3
  | 1,3 => 4 | 0,2 => 5 | 1,1 => 6 | 1,0 => 7
  | _,_ => 0

@[inline] def mulV (x y : V) : V :=
  let (a,b) := crtCoord x
  let (c,d) := crtCoord y
  indexFromCoord (a+c) (b+d)

@[inline] def edge (T : List V) (x y : V) : Bool :=
  T.any (fun t => mulV x t == y)

def permApply (p : List V) (x : V) : V := (p[x.val]?).getD 0

def isBijection (p : List V) : Bool :=
  p.length == 8 && p.eraseDups.length == 8

def graphIsoCert (T U : List V) (p : List V) : Bool :=
  isBijection p &&
  vertices.all (fun x =>
    vertices.all (fun y => edge T x y == edge U (permApply p x) (permApply p y)))

-- Exact witnesses produced independently by verify_g30_gate_b.py.
def tcTarget0 : List V := [0,1,3]
def tcTarget1 : List V := [0,2,5]
def tcTarget2 : List V := [0,2,7]
def tcTarget3 : List V := [0,4,6]
def tcTarget4 : List V := [0,5,7]

def p0 : List V := [0,2,1,7,4,5,6,3]
def p1 : List V := [0,1,2,6,3,7,4,5]
def p2 : List V := [0,1,2,3,4,5,6,7]
def p3 : List V := [0,1,4,3,2,5,7,6]
def p4 : List V := [0,1,5,4,3,2,6,7]









end CouretUnification.G30ComplexSpectrum


