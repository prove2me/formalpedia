-- Prove2me | Definitions.Def_mme_released_recursive_profile_mixture
-- name    : mme_released_recursive_profile_mixture
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-22T16:31:20.424837+00:00
-- url     : https://prove2.me/theorems/5c816927-1303-429c-a810-09be98ffb62a
-- title:
--   Recursive parent profiles from the published primitive seed
-- statement:
--   With $D=10^{12}$, define the square-child word marginal from its physical degree and published degree-two parameter. For each interior primitive parent, define its regional marginal by summing products of its two child marginals against the published split distribution, and then mix the six regions with their published weights. For boundary parents use the explicit terminal marginal. The integer denominators are respectively $D$, $D^3$, and $D^4$. The owner and shape lookup uses the same published coordinate permutation as the global literal table. These definitions reconstruct frequencies directly from the primitive seed; they do not assert an equality with the global table.
-- source:
--   Exact-seed profile bridge for the six-region global interface in More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2. Uses the already published primitive rational seed and literal supported joint counts; the recursive numerical continuation remains a separate obligation.

import Definitions.Def_mme_released_global_profile_data
open BigOperators MME MME.ReleasedGlobal
set_option autoImplicit false
namespace MME.ReleasedMixture

abbrev D : ℕ := MoreAsymmetryExactSeed.denominator
abbrev SeedTerm := MoreAsymmetryExactSeed.Term

def emptyTerm : SeedTerm := ⟨[], [], [], [], [], [], []⟩

/-- The published primitive term, indexed in the global hash orientation. -/
def term (owner : Fin 6) (s : Fin 45) : SeedTerm :=
  (![MoreAsymmetryExactSeed.owner0, MoreAsymmetryExactSeed.owner1,
      MoreAsymmetryExactSeed.owner2, MoreAsymmetryExactSeed.owner3,
      MoreAsymmetryExactSeed.owner4, MoreAsymmetryExactSeed.owner5] owner).getD
    (sourceIndex owner s).val emptyTerm

def childParameter (t : SeedTerm) (r : Fin 6) (s : List ℕ) : ℕ :=
  ((t.children.find? (fun c ↦ c.1 == r.val && c.2.1 == s)).getD (0, [], 0)).2.2

/-- Numerators on denominator D of the square-word marginal of a child
of degree d. The degree-two marginal is (p,D-2p,p). -/
def squareCount (d p x y : ℕ) : ℕ :=
  if x + y ≠ d ∨ 2 < x ∨ 2 < y then 0 else
  match d with
  | 0 => D
  | 1 => D / 2
  | 2 => if x = 1 then D - 2*p else p
  | 3 => D / 2
  | 4 => D
  | _ => 0

def opposite (t : SeedTerm) (s : List ℕ) : List ℕ :=
  (t.shape.zip s).map (fun p ↦ p.1 - p.2)

/-- Numerator on denominator D^3: split mass times the product of the two
child square-word marginals, summed over the published split list. -/
def regionCount (t : SeedTerm) (r : Fin 6) (i : Fin 3) (w : Word) : ℕ :=
  (t.splits.mapIdx (fun j s ↦
    ((t.alpha.getD r.val []).getD j 0) *
      squareCount (s.getD i.val 0) (childParameter t r s) (w 0).val (w 1).val *
      squareCount ((opposite t s).getD i.val 0) (childParameter t r (opposite t s))
        (w 2).val (w 3).val)).sum

def regionWeight (t : SeedTerm) (r : Fin 6) : ℕ := t.region.getD r.val 0

/-- The primitive boundary marginal in physical coordinates, with denominator D. -/
def boundaryCount (t : SeedTerm) (i : Fin 3) (w : Word) : ℕ :=
  if t.shape.getD i.val 0 = 0 then
    if w = (fun _ ↦ 0) then D else 0
  else
    let b := if t.shape.getD 0 0 = 0 then 1 else 0
    let v := List.ofFn (fun r : Fin 4 ↦ if i.val = b then (w r).val else 2-(w r).val)
    ((t.boundary.filter (fun p ↦ p.1 == v)).map Prod.snd).sum

/-- Full parent marginal numerator on denominator D^4, obtained solely from
the primitive seed. Boundary terms use their explicit terminal profiles. -/
def parentCount (t : SeedTerm) (i : Fin 3) (w : Word) : ℕ :=
  if t.boundary = [] then ∑ r : Fin 6, regionWeight t r * regionCount t r i w
  else D^3 * boundaryCount t i w

noncomputable def regionProfile (t : SeedTerm) (r : Fin 6) (i : Fin 3) (w : Word) : ℝ :=
  (regionCount t r i w : ℝ) / (D : ℝ)^3

noncomputable def parentProfile (t : SeedTerm) (i : Fin 3) (w : Word) : ℝ :=
  if t.boundary = [] then
    ∑ r : Fin 6, ((regionWeight t r : ℝ) / D) * regionProfile t r i w
  else (boundaryCount t i w : ℝ) / D

end MME.ReleasedMixture


