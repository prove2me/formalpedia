-- Prove2me | solution 1 for ToricCode.vWind_const
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:45:31.832264+00:00
-- url     : https://prove2.me/submissions/58100914-ba22-4ed8-91da-d84adaedced5

-- Sol generated from Geometry/ToricCode/Distance.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_Distance
import Definitions.Def_Geometry_ToricCode_Homology
import Theorems.Thm_ToricCode_vWind_succ
import Theorems.Thm_ToricCode_zmod_const_of_succ
/-!
# The `Z`-distance of the `M × N` toric code is exactly `min M N`

This is the geometric heart of the development.  For the grid cellulation of the
torus `(ℤ/M) × (ℤ/N)` we prove

  `distance M N = min M N`,

i.e. the minimal Hamming weight of a cellular one-cycle that is not a boundary
is exactly the smaller of the two side lengths.  Together with
`ToricCode.toric_homologyRank` this establishes the parameters
`[[2MN, 2, min M N]]`, specialising to the classical `[[2L², 2, L]]` for the
square torus.

## Strategy

For each `i : ZMod M` the *column cut* consists of the `N` horizontal edges
`(false, (i, y))`.  The parity of a chain on this cut is `hWind z i`.  Dually
`vWind z j` is the parity on the *row cut* of vertical edges `(true, (x, j))`.

* `hWind_const` / `vWind_const`: for a cycle these parities do not depend on the
  cut.  (This is discrete Stokes: the difference of two neighbouring cut parities
  is the sum of the vertex boundary over a column.)
* `hWind_of_boundary` / `vWind_of_boundary`: they vanish on boundaries.
* `winding_ne_zero_of_not_boundary`: conversely, a cycle with both windings zero
  *is* a boundary.  This is proved by a dimension count: the winding map
  `cycles → 𝔽₂²` is onto, so its kernel has dimension `MN - 1`, which is exactly
  the dimension of the boundary space computed in `ToricCode.Homology`.
* Hence a logical operator has odd parity on each of the `M` pairwise disjoint
  column cuts, or on each of the `N` pairwise disjoint row cuts, so it uses at
  least `min M N` edges; and the two coordinate loops, of weights `M` and `N`,
  realise the bound.
-/

open Matrix

open ToricCode

variable (M N : ℕ) [NeZero M] [NeZero N]

/-! ### Winding parities -/









/-! ### Windings vanish on boundaries -/



/-! ### The winding map and its surjectivity -/














/-! ### The kernel of the winding map is exactly the boundary space -/






/-! ### The distance -/















/-
-- !-- Lab Notes -- !--

Hypothesis (Hypothesizer).
  The previous cycle proved `distance = systole` abstractly and showed that the
  abstract homology rank cannot determine the distance.  The natural bold
  conjecture is that a genuine cellulation *does* determine it, and that the
  `M × N` torus grid realises exactly `[[2MN, 2, min M N]]`: a shortest
  noncontractible cellular loop should have to cross each of the `M` disjoint
  column cuts, or each of the `N` disjoint row cuts, an odd number of times.

Experiment (Experimenter).
  Before formalising, the square case was tested by exhaustive enumeration over
  all `2^(2L²)` binary one-chains, using the very definitions of this directory
  (`d1`, `d2`, `hammingNorm`).  Data (`min` = minimum weight of a cycle that is
  not a boundary):

    L = 1 :  #cycles =    4,  #boundaries =   1,  min = 1   (dual: min = 1)
    L = 2 :  #cycles =   32,  #boundaries =   8,  min = 2   (dual: min = 2)
    L = 3 :  #cycles = 1024,  #boundaries = 256,  min = 3   (dual: min = 3)

  These match the predicted `#cycles = 2^(L²+1)`, `#boundaries = 2^(L²-1)`,
  `min = L`, and the predicted equality of primal and dual spectra.  `L = 4`
  would require enumerating `2³²` chains and was not attempted; the general
  proof supersedes it.  The full logical weight spectra were also enumerated
  (`1,2` for `L=1`; `2,4,6` for `L=2`; `3,5,6,…,15,18` for `L=3`), refuting the
  stronger guess that all logical operators have weight `L`.

Analysis (Analyst).
  Two ingredients were needed and both survived formalisation.  (i) *Discrete
  Stokes*: summing the vertex boundary over a full column shows neighbouring cut
  parities agree, so a cycle has a well-defined pair of winding parities
  (`hWind_const`, `vWind_const`).  (ii) *A dimension count replaces an explicit
  potential function*: proving directly that a cycle with zero windings bounds
  would require constructing a face chain by integrating along paths on the
  torus, with awkward wrap-around cases.  Instead the winding map
  `cycles → 𝔽₂²` is shown to be onto, so its kernel has dimension `MN - 1`,
  which the independent computation `rank d₂ = MN - 1` identifies with the
  boundary space (`boundaries_eq_trivialWinding`).  The rank computation itself
  avoids bases entirely: `rank d₁ = rank d₁ᵀ` and the kernel of a coboundary is
  the line of constants, which is exactly connectivity of the torus graph and of
  its dual graph.  Crucially, *no step used `M = N`*: this is why the whole
  argument generalises to rectangular tori and yields `distance = min M N`.

Critique (Critic).
  Nothing here is vacuous: the lower bound `min M N ≤ hammingNorm z` genuinely
  uses the hypothesis `z ∉ boundaries`, and the value is attained, so
  `distance = min M N` is a two-sided statement.  The edge cases `M = 1` or
  `N = 1` are included and are not degenerate for the argument.  Nowhere is
  `decide` used on a statement depending on `M` or `N`; the only `decide` calls
  are on closed `𝔽₂` identities such as `1 + 1 = 0`.
-/
open ToricCode in
theorem solution{z : Edge M N → F2} (hz : (d1 M N) *ᵥ z = 0) (j : ZMod N) :
    vWind M N z j = vWind M N z 0 :=
  zmod_const_of_succ (vWind M N z) (vWind_succ M N hz) j
